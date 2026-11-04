-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.sourceCells_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:47.229352+00:00
-- url     : https://prove2.me/submissions/3370fa8f-9dbe-4db8-af90-1d1bd2d229de

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_le_fullOutputs

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution (n : ℕ) :
    sourceCells n ≤ (mu n+1)*encoderCount n := by
  calc
    _ ≤ 2*bandCount n*scheduleCount n*((mu n+1)*fullOutputs n) :=
      Nat.mul_le_mul_left _ (downset_le_fullOutputs n)
    _ = _ := by unfold encoderCount; ring
end ThreeSum.BlockSourceSharing
