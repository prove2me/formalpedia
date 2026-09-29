-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:53.012378+00:00
-- url     : https://prove2.me/submissions/5e14526e-9127-4d3e-8e15-39848912a096

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffEval_eq_eval_XCoeffEquiv

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).ncard ≤ r.totalDegree := by
  have hr' : XCoeffEquiv r ≠ 0 := by
    intro h0
    have h0' : XCoeffEquiv r = XCoeffEquiv 0 := by
      simpa using h0
    exact hr (XCoeffEquiv.injective h0')
  have hrootset_eq :
      CoeffRootSet r = (XCoeffEquiv r).rootSet ℝ := by
    ext x
    rw [Polynomial.mem_rootSet]
    constructor
    · intro hx
      refine ⟨hr', ?_⟩
      change coeffEval x r = 0 at hx
      change Polynomial.eval x (XCoeffEquiv r) = 0
      rw [coeffEval_eq_eval_XCoeffEquiv]
      exact hx
    · intro hx
      change coeffEval x r = 0
      rw [← coeffEval_eq_eval_XCoeffEquiv]
      simpa only [Polynomial.coe_aeval_eq_eval] using hx.2
  have hdeg : (XCoeffEquiv r).natDegree ≤ r.totalDegree := by
    calc
      (XCoeffEquiv r).natDegree = ((MvPolynomial.finSuccEquiv ℝ 0) r).natDegree := by
        simpa [XCoeffEquiv] using
          (Polynomial.natDegree_map_eq_of_injective
            (f := (MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.toRingHom)
            ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv.injective)
            ((MvPolynomial.finSuccEquiv ℝ 0) r))
      _ = MvPolynomial.degreeOf 0 r := by
        simpa using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
      _ ≤ r.totalDegree := MvPolynomial.degreeOf_le_totalDegree r 0
  have hroot :
      (CoeffRootSet r).ncard ≤ (XCoeffEquiv r).natDegree := by
    simpa [hrootset_eq] using (Polynomial.ncard_rootSet_le (XCoeffEquiv r) ℝ)
  exact le_trans hroot hdeg
