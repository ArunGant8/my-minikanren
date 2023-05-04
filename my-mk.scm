;; This is my attempt at implementing miniKanren
;; since the implementations available online do
;; not work. This implementation is created from
;; "The Reasoned Schemer" by William Byrd.

;; Step: 1: Creating UNIQUE variables:

(define (var name) (vector name))
(define (var? name) (vector? name))

;; An ASSOCIATION of 'a with a variable z is the pair
;;          `(,z . a)
;; A pair is an association when the car of the pair
;; is a variable. The cdr may be a variable or a value
;; containing zero or more variables.

;; A SUBSTITUTION is a special kind of list of associations.
;; An example is:
;;          `((,z . oat) (,x .nut))
;; In a substitution, an association whose cdr is also a
;; variable represents the FUSING of that association's two
;; variables.

;; EMPTY-S creates an empty substitution
(define empty-s '())

;; Note that `((,z . a) (,x . ,w) (,z . b)) is NOT a substitution
;; since our substitutions cannot contain two or more associations
;; with the same car

;; WALK is a function that, given a substitution and a variable,
;; searches for associations of that variable in the substitution.
;; It continues till it gets a non-variable, or, failing that, it
;; returns the variable with which the given variable is fused.

(define (walk v s)
  (let ((a (and (var? v) (assv v s))))
    (cond
     ((pair? a) (walk (cdr a) s))
     (else v))))

;; EXT-S extends a substitution s with an association between the
;; variable x and the value v, or it produces #f if extending the
;; substitution with the pair `(,x . ,v) would have created a cycle
;;
;; OCCURS? checks whether the variable v is either:
;;          i) the variable x; or
;;          ii) the fused to the variable x in any way

(define (ext-s x v s)
  (cond
   ((occurs? x v s) #f)
   (else (cons `(,x . ,v) s))))

(define (occurs? x v s)
  (let ((v (walk v s)))
    (cond
     ((var? v) (eqv? v x))
     ((pair? v)
      (or (occurs? x (car v) s)
          (occurs? x (cdr v) s)))
     (else #f))))

;; Now we define UNIFY using WALK and EXT-S:

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((eqv? u v) s)
     ((var? u) (ext-s u v s))
     ((var? v) (ext-s v u s))
     ((and (pair? u) (pair? v))
      (let ((s (unify (car u) (car v) s)))
        (and s
             (unify (cdr u) (cdr v) s))))
     (else #f))))

;; We need one more idea: STREAMS
;; A stream is either:
;;      i) The empty list
;;      ii) A pair whose cdr is a stream, or
;;      iii) A SUSPENSION
;;
;; A suspension is a function formed from
;; (lambda () body) where (body)
;; is a stream

;; Defining ==
(define (== u v)
  (lambda (s)
    (let ((s (unify u v s)))
      (if s `(,s) '()))))

;; What == produces is a GOAL. Below are two more goals:
(define success
  (lambda (s)
    `(,s)))

(define fail
  (lambda (s)
    `()))

;; A GOAL is a function that expects a substitution
;; and, if it returns, produces a stream of substitutions

;; We now define some functions that generate goals
(define (disj2 g1 g2)
  (lambda (s)
    (append-inf (g1 s) (g2 s))))

(define (append-inf s-inf t-inf)
  (cond
   ((null? s-inf) t-inf)
   ((pair? s-inf)
    (cons (car s-inf)
          (append-inf (cdr s-inf) t-inf)))
   (else (lambda ()
           (append-inf t-inf (s-inf))))))

;; Now we define NEVERO, a relation that always fails
(define (nevero)
  (lambda (s)
    (lambda ()
      ((nevero) s))))

;; Now we define ALWAYSO, a goal that always succeeds
(define (alwayso)
  (lambda (s)
    (lambda ()
      ((disj2 success (alwayso)) s))))

;; Now we write functions for producing lists of values from
;; streams. The most basic of these is TAKE-INF
(define (take-inf n s-inf)
  (cond
   ((and n (zero? n)) '())
   ((null? s-inf) '())
   ((pair? s-inf)
    (cons (car s-inf)
          (take-inf (and n (sub1 n))
                    (cdr s-inf))))
   (else (take-inf n (s-inf)))))

(define (conj2 g1 g2)
  (lambda (s)
    (append-map-inf g2 (g1 s))))

(define (append-map-inf g s-inf)
  (cond
   ((null? s-inf) '())
   ((pair? s-inf)
    (append-inf (g (car s-inf))
                (append-map-inf g (cdr s-inf))))
   (else (lambda ()
           (append-map-inf g (s-inf))))))

;; Now we define CALL/FRESH to introduce variables
(define (call/fresh name f)
  (f (var name)))

;; We use distinct symbols for variables when PRESENTING
;; them: every variable we present is presented as a
;; corresponding symbol: an underscore followed by a
;; natural number. We call these REIFIED variables
(define (reify-name n)
  (string->symbol
   (string-append "_"
                  (number->string n))))

;; We now define WALK*, which walks every value in the cdr
;; of an association. For example,
;;    (walk* w
;;      `((,x . b) (,z . y) (,w . (,x e ,z))))
;; evaluates to `(b e ,y) instead of `(,x e ,z)

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
     ((var? v) v)
     ((pair? v)
      (cons
       (walk* (car v) s)
       (walk* (cdr v) s)))
     (else v))))

;; REIFY-S, defined below, unifies variables with reified ones
(define (reify-s v r)
  (let ((v (walk v r)))
    (cond
     ((var? v)
      (let ((n (length r)))
        (let ((rn (reify-name n)))
          (cons `(,v . ,rn) r))))
     ((pair? v)
      (let ((r (reify-s (car v) r)))
        (reify-s (cdr v) r)))
     (else r))))

(define (reify v)
  (lambda (s)
    (let ((v (walk* v s)))
      (let ((r (reify-s v empty-s)))
        (walk* v r)))))

;; Now comes one of the main functions: RUN-GOAL that produces
;; a list of values after evaluating goals
(define (run-goal n g)
  (take-inf n (g empty-s)))

;; Now for CONDA and CONDU
;; IFTE = IF-Then-Else

(define (ifte g1 g2 g3)
  (lambda (s)
    (let loop ((s-inf (g1 s)))
      (cond
       ((null? s-inf) (g3 s))
       ((pair? s-inf)
        (append-map-inf g2 s-inf))
       (else (lambda ()
               (loop (s-inf))))))))

;; ONCE: Returns a goal that succeeds ONCE, producing a stream
;; of a single substitution

(define (once g)
  (lambda (s)
    (let loop ((s-inf (g s)))
      (cond
       ((null? s-inf) '())
       ((pair? s-inf)
        (cons (car s-inf) '()))
       (else (lambda ()
            (loop (s-inf))))))))

;; CONNECTING THE WIRES: (Extending Scheme syntax using Macros)

(define-syntax disj
  (syntax-rules ()
    ((disj) fail)
    ((disj g) g)
    ((disj g0 g ...) (disj2 g0 (disj g ...)))))

(define-syntax conj
  (syntax-rules ()
    ((conj) success)
    ((conj g) g)
    ((conj g0 g ...) (conj2 g0 (conj g ...)))))

(define-syntax defrel
  (syntax-rules ()
    ((defrel (name x ...) g ...)
     (define (name x ...)
       (lambda (s)
         (lambda ()
           ((conj g ...) s)))))))

(define-syntax run
  (syntax-rules ()
    ((run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                     (== `(,x0 ,x ...) q) g ...)))
    ((run n q g ...)
     (let ((q (var 'q)))
       (map (reify q)
            (run-goal n (conj g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((run* q g ...) (run #f q g ...))))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () g ...) (conj g ...))
    ((fresh (x0 x ...) g ...)
     (call/fresh 'x0
                 (lambda (x0)
                   (fresh (x ...) g ...))))))

(define-syntax conde
  (syntax-rules ()
    ((conde (g ...) ...)
     (disj (conj g ...) ...))))

(define-syntax conda
  (syntax-rules ()
    ((conda (g0 g ...)) (conj g0 g ...))
    ((conda (g0 g ...) ln ...)
     (ifte g0 (conj g ...) (conda ln ...)))))

(define-syntax condu
  (syntax-rules ()
    ((condu (g0 g ...) ...)
     (conda ((once g0) g ...) ...))))
