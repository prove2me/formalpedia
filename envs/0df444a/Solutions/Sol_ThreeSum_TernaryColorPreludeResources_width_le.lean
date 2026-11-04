-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.width_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:01:58.880943+00:00
-- url     : https://prove2.me/submissions/c27dad91-3012-4f22-b24c-0e507070774a

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (n : ℕ) : width n≤ n+1 := by
  unfold width
  exact Nat.add_le_add_right (LightScales.inputBits_le_self n) 1
end ThreeSum.TernaryColorPreludeResources
