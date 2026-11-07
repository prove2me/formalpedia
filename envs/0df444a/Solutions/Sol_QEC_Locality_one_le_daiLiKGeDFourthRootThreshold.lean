-- Prove2me | solution 1 for QEC.Locality.one_le_daiLiKGeDFourthRootThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:26:16.493195+00:00
-- url     : https://prove2.me/submissions/b9a8d568-b9ae-4bc7-8c6d-dd074e535075

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_nonneg
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_pow_four

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    {k d n : ℝ} (hk : 0 ≤ k) (hn : 0 < n)
    (habove : (100 : ℝ) ^ 4 * n ≤ k * d ^ 2) :
    1 ≤ daiLiKGeDFourthRootThreshold k d n := by
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  have hRatioLarge : (100 : ℝ) ^ 4 ≤ k * d ^ 2 / n := by
    apply (le_div_iff₀ hn).2
    nlinarith
  have hRootNonneg : 0 ≤ daiLiFourthRoot (k * d ^ 2 / n) :=
    daiLiFourthRoot_nonneg _
  have hRootPow : daiLiFourthRoot (k * d ^ 2 / n) ^ 4 = k * d ^ 2 / n :=
    daiLiFourthRoot_pow_four _ hRatio
  have hRootLarge : (100 : ℝ) ≤ daiLiFourthRoot (k * d ^ 2 / n) := by
    by_contra h
    have hRootSmall : daiLiFourthRoot (k * d ^ 2 / n) < 100 := lt_of_not_ge h
    have hSquareSmall : daiLiFourthRoot (k * d ^ 2 / n) ^ 2 < 100 ^ 2 := by
      nlinarith [sq_nonneg (daiLiFourthRoot (k * d ^ 2 / n) - 100)]
    have hFourthSmall : daiLiFourthRoot (k * d ^ 2 / n) ^ 4 < 100 ^ 4 := by
      nlinarith [sq_nonneg (daiLiFourthRoot (k * d ^ 2 / n) ^ 2 - 100 ^ 2)]
    nlinarith
  unfold daiLiKGeDFourthRootThreshold
  linarith
end QEC.Locality
