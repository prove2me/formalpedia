-- Prove2me | solution 1 for TaoFivePrimes.representationCount_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:40:45.767669+00:00
-- url     : https://prove2.me/submissions/91e1f73a-7a7f-4dfe-8f30-f2d8dbfdd6be

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

private lemma siftedVonMangoldt_nonneg (N n : ℕ) : 0 ≤ siftedVonMangoldt N n := by
  unfold siftedVonMangoldt
  split
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

private lemma eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := le_max_left _ _

private lemma eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split
  · have : (0 : ℝ) ≤ max 0 (Real.log 2 - |Real.log (2 * t)|) := le_max_left _ _
    linarith
  · exact le_rfl

/-- Every summand of `representationCount` is a product of nonnegative factors,
so the count is nonnegative for all `x` and `H`, with no hypotheses. -/
theorem solution (x H : ℕ) : 0 ≤ representationCount x H := by
  unfold representationCount
  refine Finset.sum_nonneg fun n₁ _ => Finset.sum_nonneg fun n₂ _ =>
    Finset.sum_nonneg fun n₃ _ => Finset.sum_nonneg fun h₁ _ =>
    Finset.sum_nonneg fun h₂ _ => Finset.sum_nonneg fun h₃ _ => ?_
  split
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (siftedVonMangoldt_nonneg _ _) (eta1_nonneg _)) (siftedVonMangoldt_nonneg _ _))
      (eta1_nonneg _)) (siftedVonMangoldt_nonneg _ _)) (eta0_nonneg _)
  · exact le_rfl
