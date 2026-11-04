-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalDimensions.r_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:46.844531+00:00
-- url     : https://prove2.me/submissions/b3937bef-d55d-4c58-bf9e-0076e3df4cfb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedGlobalDimensions
theorem _root_.solution {M : ℕ} (hM : 1<M) (n : ℕ) : r M n≤n^2 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self hM).le
end ThreeSum.LightWeightedGlobalDimensions
