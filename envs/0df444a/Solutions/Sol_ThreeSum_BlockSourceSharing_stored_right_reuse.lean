-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.stored_right_reuse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:22.219927+00:00
-- url     : https://prove2.me/submissions/914ce8d9-192a-46c6-9e3f-2db389aa548f

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_BlockSourceSharing_rightSource_eq_of_occurrences

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P d : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (rightSource P d B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (rightSource P d B b q') (J*(512*h)) := by
  rw [← rightSource_eq_of_occurrences P d B b he]
  exact hs
end ThreeSum.BlockSourceSharing
