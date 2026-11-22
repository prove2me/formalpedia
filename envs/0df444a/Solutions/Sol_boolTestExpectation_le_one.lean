-- Prove2me | solution 1 for boolTestExpectation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:44.941532+00:00
-- url     : https://prove2.me/submissions/ccb8e427-ac3d-4f95-9bd3-f99d3bdbac35

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution {H : Type*} [Fintype H]
    (μ : FinitePMF H) (f : H → Bool) :
    boolTestExpectation μ f ≤ 1 := by
  simp only [boolTestExpectation, trueExpectation]
  calc ∑ h : H, μ.prob h * (if f h then (1 : ℝ) else 0)
      ≤ ∑ h : H, μ.prob h := Finset.sum_le_sum fun h _ =>
        mul_le_of_le_one_right (μ.prob_nonneg h) (by split_ifs <;> norm_num)
    _ = 1 := μ.prob_sum_one
