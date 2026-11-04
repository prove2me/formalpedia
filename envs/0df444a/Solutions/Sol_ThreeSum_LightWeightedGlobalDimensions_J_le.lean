-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalDimensions.J_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:55:41.438818+00:00
-- url     : https://prove2.me/submissions/9d410e75-521b-410b-b013-6240a6ee3af3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_r_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedGlobalDimensions
theorem _root_.solution {M b : ℕ} (hM : 1<M) (hb : 1<b) (n U : ℕ) : J M b n U≤n^2+4*U+3 := by
  have hr := r_le hM n
  have hc : Nat.clog b (4*U+1)≤4*U+1 := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le
  unfold J paddedLength digitLength
  omega
end ThreeSum.LightWeightedGlobalDimensions
