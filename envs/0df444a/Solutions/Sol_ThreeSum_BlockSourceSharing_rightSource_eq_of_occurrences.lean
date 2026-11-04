-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.rightSource_eq_of_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:57.319083+00:00
-- url     : https://prove2.me/submissions/c1d5eafa-cfc9-4356-a4d3-379be3171ab1

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
    {h J : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) {q q' : GlobalOutput h J}
    (he : outputOccurrences q = outputOccurrences q') :
    rightSource P d B b q = rightSource P d B b q' := by
  unfold rightSource
  rw [he]
end ThreeSum.BlockSourceSharing
