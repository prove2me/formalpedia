-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.coeffEval_eq_eval_XCoeffEquiv
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:50.475576+00:00
-- url     : https://prove2.me/submissions/8d8a93dc-554f-413d-ad71-2eb4833e13fd

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (x : ℝ) (r : XCoeff) :
    Polynomial.eval x (XCoeffEquiv r) = coeffEval x r := by
  refine MvPolynomial.induction_on
    (motive := fun r => Polynomial.eval x (XCoeffEquiv r) = coeffEval x r) r ?_ ?_ ?_
  · intro a
    simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
    change MvPolynomial.coeff (0 : Fin 0 →₀ ℕ) (MvPolynomial.C a) = a
    rw [MvPolynomial.coeff_C]
    simp
  · intro r s hr hs
    simp [hr, hs]
  · intro r n hr
    fin_cases n
    rw [map_mul, Polynomial.eval_mul]
    rw [hr]
    simp [XCoeffEquiv, coeffEval, MvPolynomial.finSuccEquiv_apply]
