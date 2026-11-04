-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:24.473044+00:00
-- url     : https://prove2.me/submissions/0eb6f8e3-8359-4d7d-98c2-65f316763efb

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_BlockSourceSharing_occurrence_card

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by
  rw [occurrence_card,scheduleCount,replicatedHalf,localLength,scheduleSize_eq_length]
end ThreeSum.BlockSourceSharing
