-- Prove2me | solution 1 for ThreeSum.BlockSourceSharing.stored_left_reuse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:28.044633+00:00
-- url     : https://prove2.me/submissions/8709029c-5261-4d90-8e63-aea3ac8cb4e5

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Theorems.Thm_ThreeSum_BlockSourceSharing_leftSource_eq_of_occurrences

set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceSharing
open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds
namespace ThreeSum.BlockSourceSharing
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (he : outputOccurrences q = outputOccurrences q')
    (hs : LightZetaStages.StoredThrough μ base cut (leftSource P B b q) (J*(512*h))) :
    LightZetaStages.StoredThrough μ base cut (leftSource P B b q') (J*(512*h)) := by
  rw [← leftSource_eq_of_occurrences P B b he]
  exact hs
end ThreeSum.BlockSourceSharing
