-- Prove2me | solution 1 for continuous_eval_divByMonic_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:24.844839+00:00
-- url     : https://prove2.me/submissions/2e8ccca3-5210-4cb5-86a9-272b8087b67e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution (p : Polynomial ℂ) :
    Continuous (fun x : ℂ × ℂ =>
      Polynomial.eval x.2 (p /ₘ (Polynomial.X - Polynomial.C x.1))) := by
  have hfun :
      (fun x : ℂ × ℂ =>
        Polynomial.eval x.2 (p /ₘ (Polynomial.X - Polynomial.C x.1))) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
        (∑ j ∈ Finset.Icc (i + 1) p.natDegree,
          x.1 ^ (j - (i + 1)) * p.coeff j) * x.2 ^ i := by
    funext x
    rw [Polynomial.eval_eq_sum_range' (n := p.natDegree + 1)]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [Polynomial.coeff_divByMonic_X_sub_C]
    · rw [Polynomial.natDegree_divByMonic p
        (Polynomial.monic_X_sub_C x.1), Polynomial.natDegree_X_sub_C]
      omega
  rw [hfun]
  fun_prop
