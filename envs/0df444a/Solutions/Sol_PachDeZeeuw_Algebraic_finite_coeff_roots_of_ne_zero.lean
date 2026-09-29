-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.finite_coeff_roots_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:52.495355+00:00
-- url     : https://prove2.me/submissions/4d9a1c14-53c5-4896-8f58-748ee4e42443

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_coeffEval_eq_eval_XCoeffEquiv

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (r : XCoeff) (hr : r ≠ 0) :
    (CoeffRootSet r).Finite := by
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
  have hfinRoots : {x : ℝ | Polynomial.IsRoot (XCoeffEquiv r) x}.Finite :=
    Polynomial.finite_setOfPred_isRoot hr'
  have hsubset : (XCoeffEquiv r).rootSet ℝ ⊆ {x : ℝ | Polynomial.IsRoot (XCoeffEquiv r) x} := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    exact hx.2
  rw [hrootset_eq]
  exact Set.Finite.subset hfinRoots hsubset
