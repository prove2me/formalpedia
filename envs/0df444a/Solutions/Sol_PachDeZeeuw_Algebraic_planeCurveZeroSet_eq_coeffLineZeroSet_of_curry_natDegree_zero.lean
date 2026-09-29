-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.planeCurveZeroSet_eq_coeffLineZeroSet_of_curry_natDegree_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:54.632732+00:00
-- url     : https://prove2.me/submissions/86b608ec-83f4-4347-9c5b-8bb7b0cf1e1c

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_eval_eq_specialized_eval
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_CoeffLineZeroSet
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_PlaneCurveZeroSet

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0) :
    PlaneCurveZeroSet h = CoeffLineZeroSet ((Curry0 h).coeff 0) := by
  have hC : Curry0 h = Polynomial.C ((Curry0 h).coeff 0) := by
    simpa using (Polynomial.eq_C_of_natDegree_eq_zero hdeg0)
  ext z
  constructor
  · intro hz
    have hz' : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) h) = 0 := by
      rw [← eval_eq_specialized_eval h z]
      simpa using hz
    have hspec :
        Specialized0 (coeffCoord z) h =
          Polynomial.C
            (MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) ((Curry0 h).coeff 0)) := by
      rw [Specialized0, hC]
      simp [coeffEval]
    rw [mem_CoeffLineZeroSet]
    change MvPolynomial.eval (fun _ : Fin 1 ↦ coeffCoord z) ((Curry0 h).coeff 0) = 0
    rw [hspec] at hz'
    simpa using hz'
  · intro hz
    rw [mem_PlaneCurveZeroSet]
    rw [eval_eq_specialized_eval h z]
    change MvPolynomial.eval (fun _ : Fin 1 ↦ coeffCoord z) ((Curry0 h).coeff 0) = 0 at hz
    have hspec :
        Specialized0 (coeffCoord z) h =
          Polynomial.C
            (MvPolynomial.eval (fun _ : Fin 1 => coeffCoord z) ((Curry0 h).coeff 0)) := by
      rw [Specialized0, hC]
      simp [coeffEval]
    rw [hspec]
    simpa using hz
