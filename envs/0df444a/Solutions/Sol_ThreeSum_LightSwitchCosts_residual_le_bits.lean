-- Prove2me | solution 1 for ThreeSum.LightSwitchCosts.residual_le_bits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:47.386741+00:00
-- url     : https://prove2.me/submissions/285643b2-ad6b-4281-b1a6-c04bc1001f62

import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingCostBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Theorems.Thm_ThreeSum_LightScales_totalSize_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchCosts
open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology
namespace ThreeSum.LightSwitchCosts
theorem _root_.solution (n j : ℕ) : Switch.residualSize n j ≤ inputBits n := by
  calc
    _ ≤ blockCount (inputBits n)*muZero n :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ inputBits n := LightScales.totalSize_le_self (inputBits n)
end ThreeSum.LightSwitchCosts
