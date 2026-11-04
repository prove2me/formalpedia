-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentWeightBounds.right_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:17:01.158587+00:00
-- url     : https://prove2.me/submissions/1f794de9-bd53-4026-a47d-11232d49418c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
namespace ThreeSum.WeightedGlobalMomentWeightBounds
theorem _root_.solution {U K k j : ℕ} (hk : k≤K) :
    max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤(rightWord U K : ℤ) := by
  have hp := pow_le_pow_right₀ (show (1 : ℤ)≤U+1 by omega) (show k-j≤K by omega)
  have hm := mul_le_mul_of_nonneg_left hp (by decide : (0 : ℤ)≤2)
  unfold rightWord
  push_cast
  apply max_le <;> nlinarith [show (0 : ℤ)≤2*((U : ℤ)+1)^K by positivity]
end ThreeSum.WeightedGlobalMomentWeightBounds
