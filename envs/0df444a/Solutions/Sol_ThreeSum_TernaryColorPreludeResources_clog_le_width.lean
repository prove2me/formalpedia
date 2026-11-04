-- Prove2me | solution 1 for ThreeSum.TernaryColorPreludeResources.clog_le_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:00.215203+00:00
-- url     : https://prove2.me/submissions/902b2498-9856-40a6-bfe4-31d6c7bd091d

import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryColorPreludeResources_w3sum_ac885d1
import Theorems.Thm_ThreeSum_LightColorParametersCosts_width_sufficient


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryColorPreludeResources
open Light LightTernaryColorPrelude LightColorParametersCosts StageBounds
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace ThreeSum.TernaryColorPreludeResources
theorem _root_.solution (n : ℕ) : Nat.clog 2 n≤ width n :=
  Nat.clog_le_of_le_pow (width_sufficient n)
end ThreeSum.TernaryColorPreludeResources
