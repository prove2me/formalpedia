-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.leftSource_eq_of_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:16.557494+00:00
-- url     : https://prove2.me/submissions/8acabf0a-41c9-4bbf-896e-eb44e0a83444

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by
  unfold leftSource
  rw [he]
end ThreeSum.BlockSourceSharing
