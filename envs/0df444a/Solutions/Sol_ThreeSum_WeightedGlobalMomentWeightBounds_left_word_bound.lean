-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentWeightBounds.left_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:34:37.723882+00:00
-- url     : https://prove2.me/submissions/02453324-7571-461d-bc4f-a1e87345be2e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_choose_bound

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
namespace ThreeSum.WeightedGlobalMomentWeightBounds
theorem _root_.solution {U K k j : ℕ} (hk : k≤K) (hj : j≤k) :
    max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤(leftWord U K : ℤ) := by
  have hc := choose_bound (j := j) hk
  have hp := pow_le_pow_right₀ (show (1 : ℤ)≤U+2 by omega) (show j≤K by omega)
  have hm := mul_le_mul (show (2 : ℤ)*(k.choose j+1)≤2*(2^K+1) by omega)
    hp (by positivity) (by positivity : (0 : ℤ)≤2*(2^K+1))
  unfold leftWord
  push_cast
  apply max_le <;> nlinarith [show (0 : ℤ)≤2*(2^K+1)*((U : ℤ)+2)^K by positivity]
end ThreeSum.WeightedGlobalMomentWeightBounds
