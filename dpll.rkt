;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname dpll) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(define-struct and-op [left right])
(define-struct or-op [left right])
(define-struct not-op [val])
; A BooleanFormula is one of:
; - Boolean
; - Symbol
; - (make-and-op BooleanFormula BooleanFormula)
; - (make-or-op BooleanFormula BooleanFormula)
; - (make-not-op BooleanFormula)
; and represents a boolean function with free variables

(define ex-bf-1 'x)
(define ex-bf-2 (make-not-op 'x))
(define ex-bf-3 (make-and-op 'x 'y))
(define ex-bf-4 (make-or-op 'x 'y))

; BooleanFormula -> ???
(define (bf-temp bf)
  (cond
    [(boolean? bf) ...]
    [(symbol? bf) ...]
    [(and-op? bf) (... (bf-temp (and-op-left bf)) ... (bf-temp (and-op-right bf)) ...) ]
    [(or-op? bf) (... (bf-temp (or-op-left bf)) ... (bf-temp (or-op-right bf)) ...)]
    [(not-op? bf) (... (bf-temp (not-op-val bf)) ...)]))


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

; satisfiable? : BooleanFormula -> Boolean
; sat solves stuff
(define (satisfiable? bf)
  (satisfiable-helper? bf (find-free-vars bf)))

(check-expect (satisfiable?  ex-bf-4) #t)
(check-expect (satisfiable? (make-and-op 'x 'x)) #t)
(check-expect (satisfiable? ex-bf-3) #t)
(check-expect (satisfiable? (make-and-op 'x (make-not-op 'x))) #f)


;; find-free-vars : BooleanFormula -> [List-of Symbol]
;; computes a list of all the variables that exist within the boolean formula
(define (find-free-vars bf)
  (cond
    [(boolean? bf) '()]
    [(symbol? bf) (list bf)]
    [(and-op? bf) (append (find-free-vars (and-op-left bf)) (find-free-vars (and-op-right bf)))]
    [(or-op? bf) (append (find-free-vars (or-op-left bf)) (find-free-vars (or-op-right bf)))]
    [(not-op? bf) (find-free-vars (not-op-val bf))]))

(check-expect (find-free-vars  ex-bf-1) (list 'x))
(check-expect (find-free-vars  ex-bf-2) (list 'x))
(check-expect (find-free-vars  ex-bf-3) (list 'x 'y))
(check-expect (find-free-vars  ex-bf-4) (list 'x 'y))

;; satisfiable-helper? : BooleanFormula [List-of Symbol] -> Boolean
;; computes a list of all the variables that exist within the boolean formula
;; INVARIANT: all symbols in free-vars exist within bf 
(define (satisfiable-helper? bf free-vars)
  (cond
    [(consistent-literals? bf) #t]
    [(empty? free-vars) #f]
    [else (or (satisfiable-helper? (substitute (first free-vars) #t bf) (rest free-vars))
              (satisfiable-helper? (substitute (first free-vars) #f bf) (rest free-vars)))]))

(check-expect (satisfiable-helper?  ex-bf-1 empty) #f)
(check-expect (satisfiable-helper?  ex-bf-2 (list 'x)) #t)
(check-expect (satisfiable-helper?  ex-bf-3 (list 'x)) #f)
(check-expect (satisfiable-helper?  ex-bf-3 (list 'x 'y)) #t)
(check-expect (satisfiable-helper?  ex-bf-4 (list 'x)) #f)
(check-expect (satisfiable-helper?  ex-bf-4 (list 'x 'y)) #t)


;; consistent-literals? : BooleanFormula -> Boolean
;; does the boolean formula contain no variables and evaluates to true?
(define (consistent-literals? bf)
  (and (only-literals? bf) (consistent? bf)))

(check-expect (consistent-literals?  ex-bf-1) #f)
(check-expect (consistent-literals?  (make-and-op #t #t)) #t)
(check-expect (consistent-literals?  (make-or-op #t #f)) #t)
(check-expect (consistent-literals?  (make-not-op #f)) #t)
(check-expect (consistent-literals?  ex-bf-2) #f)
(check-expect (consistent-literals?  ex-bf-3) #f)
(check-expect (consistent-literals?  ex-bf-4) #f)


;; contains-no-literals? : BooleanFormula -> Boolean
;; does the boolean formula contain no variables?
(define (only-literals? bf)
  (cond
    [(boolean? bf) #t]
    [(symbol? bf) #f]
    [(and-op? bf) (and (only-literals? (and-op-left bf)) (only-literals? (and-op-right bf)))]
    [(or-op? bf) (and (only-literals? (or-op-left bf)) (only-literals? (or-op-right bf)))]
    [(not-op? bf) (only-literals? (not-op-val bf))]))

(check-expect (only-literals?  ex-bf-1) #f)
(check-expect (only-literals?  (make-and-op #t #t)) #t)
(check-expect (only-literals?  (make-or-op #t #f)) #t)
(check-expect (only-literals?  (make-not-op #t)) #t)
(check-expect (only-literals?  ex-bf-2) #f)
(check-expect (only-literals?  ex-bf-3) #f)
(check-expect (only-literals?  ex-bf-4) #f)

;; consistent? : BooleanFormula -> Boolean
;; does the boolean formula evaluate to true?
;; INVARIANT: bf must not contain any variables
(define (consistent? bf)
  (cond
    [(boolean? bf) bf]
    [(symbol? bf) (error "contains a non-literal")]
    [(and-op? bf) (and (consistent? (and-op-left bf)) (consistent? (and-op-right bf)))]
    [(or-op? bf) (or (consistent? (or-op-left bf)) (consistent? (or-op-right bf)))]
    [(not-op? bf) (not (consistent? (not-op-val bf)))]))

(check-error (consistent?  ex-bf-1) "contains a non-literal")
(check-error (consistent?  ex-bf-2) "contains a non-literal")
(check-error (consistent?  ex-bf-3) "contains a non-literal")
(check-error (consistent?  ex-bf-4) "contains a non-literal")
(check-expect (consistent?  (make-and-op #t #t)) #t)
(check-expect (consistent?  (make-and-op #f #t)) #f)
(check-expect (consistent?  (make-or-op #t #f)) #t)
(check-expect (consistent?  (make-or-op #f #f)) #f)
(check-expect (consistent?  (make-not-op #t)) #f)
(check-expect (consistent?  (make-not-op #f)) #t)


;; substitute : Symbol Boolean BooleanFormula -> BooleanFormula
;; computes the equivalent boolean formula where all occurances of var have been replaced by val
(define (substitute var val bf)
  (cond
    [(boolean? bf) bf]
    [(symbol? bf) (if (symbol=? bf var) val bf)]
    [(and-op? bf) (make-and-op (substitute var val (and-op-left bf)) (substitute var val (and-op-right bf)))]
    [(or-op? bf) (make-or-op (substitute var val (or-op-left bf)) (substitute var val (or-op-right bf)))]
    [(not-op? bf) (make-not-op (substitute var val (not-op-val bf)))]))

(check-expect (substitute  'x #f ex-bf-1) #f)
(check-expect (substitute  'y #t ex-bf-3) (make-and-op 'x #t))
(check-expect (substitute  'y #f ex-bf-4) (make-or-op 'x #f))
(check-expect (substitute  'x #t ex-bf-4) (make-or-op #t 'y))
(check-expect (substitute  'x #t ex-bf-3) (make-and-op #t 'y))

