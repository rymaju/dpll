;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname dpll) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))


#|
Full imperative pseudocode:
https://en.wikipedia.org/wiki/DPLL_algorithm#Implementations_and_applications
function DPLL(Φ)
    if Φ is a consistent set of literals then
        return true;
    if Φ contains an empty clause then
        return false;
    for every unit clause {l} in Φ do
       Φ ← unit-propagate(l, Φ);
    for every literal l that occurs pure in Φ do
       Φ ← pure-literal-assign(l, Φ);
    l ← choose-literal(Φ);
    return DPLL(Φ ∧ {l}) or DPLL(Φ ∧ {not(l)});

Note we are skipping the simplification step and the invariant that we must be in CNF form
Functional ISL pseudocode:
satisfiable:
    get a list of all the variables
    call helper with the formula and its free variables
    if the formula only contains literals then we can evaluate it, if it is evaluated to #t then it is satisfiable
    for the first variable, substitute all occurances of it with #t or #f and recur with the rest of the variables
|#



(define-struct not-op [val])
;; A Value is one of:
;; - Boolean
;; - Symbol
;; - (make-not-op Symbol)

;; A Clause is [List-of Value]

;; A CNF is a [List-of Clause]


(define ex-cnf-1 '())
(define ex-cnf-2 '((#f #f w))) 
(define ex-cnf-3 '((#f #f w) (x y z) (#t) ))
(define ex-cnf-4 '((#f #f w) (x y z) (#t) ()))
(define ex-cnf-5 `((x) (,(make-not-op 'x)) (#t) ()))

;; satisfiable? : CNF -> Boolean
;; determines if some combination of variables will make the formula evaluate to true
(define (satisfiable? cnf)
  (satisfiable-helper? cnf (find-free-vars cnf)))

(check-expect (satisfiable? ex-cnf-1) #t)
(check-expect (satisfiable? ex-cnf-2) #t)
(check-expect (satisfiable? ex-cnf-3) #t)
(check-expect (satisfiable? ex-cnf-4) #f)
(check-expect (satisfiable? ex-cnf-5) #f)
(check-expect (satisfiable? '(() (#t))) #f)
(check-expect (satisfiable? '((x y z) (#f))) #f)
(check-expect (satisfiable? `((x ,(make-not-op 'y) z))) #t)



;; find-free-vars : CNF -> [List-of Symbol]
;; computes a list of all the variables that exist within the boolean formula
(define (find-free-vars cnf)
  (cond
    [(empty? cnf) empty]
    [else (append (find-free-vars-clause (first cnf))
                  (find-free-vars (rest cnf)))]))

(check-expect (find-free-vars ex-cnf-4) '(w x y z))

(define (find-free-vars-clause clause)
  (cond
    [(empty? clause) empty]
    [else (append (find-free-vars-value (first clause))
                  (find-free-vars-clause (rest clause)))]))

(define (find-free-vars-value value)
  (cond 
     [(boolean? value) empty]
     [(symbol? value) (list value)]
     [(not-op? value) (list (not-op-val value))]))

;; satisfiable-helper? : CNF [List-of Symbol] -> Boolean
;; computes a list of all the variables that exist within the boolean formula
;; INVARIANT: all symbols in free-vars exist within bf and all symbols in bf exist in free-vars
(define (satisfiable-helper? cnf free-vars)
  (cond
    [(consistent-literals? cnf) #t]
    [(empty-clause? cnf) #f]
    [(empty? free-vars) #f]
    [else (or (satisfiable-helper? (substitute (first free-vars) #t cnf) (rest free-vars))
              (satisfiable-helper? (substitute (first free-vars) #f cnf) (rest free-vars)))]))


;; consistent-literals? : CNF -> Boolean
;; does the boolean formula contain no variables and evaluate to true?
(define (consistent-literals? bf)
  (and (only-literals? bf) (consistent? bf)))


;; contains-no-literals? : CNF -> Boolean
;; does the boolean formula contain no variables?
(define (only-literals? cnf)
  (andmap (lambda (clause)
            (andmap boolean? clause))
            cnf))

(check-expect (only-literals?  '()) #t)
(check-expect (only-literals?  '((#t #t) (#f #t))) #t)
(check-expect (only-literals?  ex-cnf-4) #f)


;; consistent? : BooleanFormula -> Boolean
;; does the boolean formula evaluate to true?
;; INVARIANT: bf must not contain any variables
(define (consistent? cnf)
  (andmap (lambda (clause) (ormap (lambda (v) v) clause)) cnf))

(check-expect (consistent? '()) #t)
(check-expect (consistent? '(())) #f)
(check-expect (consistent? '((#t #t #t))) #t)
(check-expect (consistent? '((#t #t #t) (#t #f #t))) #t)
(check-expect (consistent? '((#t #t #t) (#t #t #t) ())) #f)


(define (empty-clause? cnf)
  (ormap empty? cnf))


;; substitute : Symbol Boolean BooleanFormula -> BooleanFormula
;; computes the equivalent boolean formula where all occurances of var have been replaced by val
(define (substitute var val cnf)
  (map (lambda (clause)
         (map (lambda (expr) (substitute-helper var val expr))
                clause))
         cnf))
;; substitute-helper : Symbol Boolean Value -> Boolean
(define (substitute-helper var val expr)
  (cond
    [(boolean? expr) expr]
    [(symbol? expr) (if (symbol=? expr var) val expr)]
    [(not-op? expr) (if (symbol=? (not-op-val expr) var) (not val) expr)]))



