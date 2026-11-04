-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentWeightBounds.choose_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:15:51.405446+00:00
-- url     : https://prove2.me/submissions/4932f0cb-90b7-4934-85b1-9c949f762427

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory
namespace ThreeSum.WeightedGlobalMomentWeightBounds
theorem _root_.solution {k j K : ℕ} (hk : k≤K) : (k.choose j : ℤ)≤(2 : ℤ)^K := by
  have hc := (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by decide : 1≤2) hk)
  exact_mod_cast hc
end ThreeSum.WeightedGlobalMomentWeightBounds
