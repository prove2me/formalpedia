-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_curry_natDegree_zero_root
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:51.356168+00:00
-- url     : https://prove2.me/submissions/d5c6d34d-9fa7-44bc-8fd8-b8a9ee323ba2

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_specialized_zero

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    CoeffLineFactor x ∣ h := by
  have hspec : Specialized0 x h = 0 := by
    rw [Specialized0, Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
    simp [coeffEval, hxroot]
  exact coeffLineFactor_dvd_of_specialized_zero h x hspec
