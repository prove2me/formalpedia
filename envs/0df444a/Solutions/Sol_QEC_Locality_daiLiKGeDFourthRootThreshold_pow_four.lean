-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDFourthRootThreshold_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:26:17.603862+00:00
-- url     : https://prove2.me/submissions/2abcf7d2-8610-49cc-9991-2438f32c4bf4

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_pow_four

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    {k d n : ℝ} (hk : 0 ≤ k) (hn : 0 < n) :
    daiLiKGeDFourthRootThreshold k d n ^ 4 =
      k * d ^ 2 / (100 ^ 4 * n) := by
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  rw [daiLiKGeDFourthRootThreshold]
  rw [div_pow, daiLiFourthRoot_pow_four _ hRatio]
  field_simp
end QEC.Locality
