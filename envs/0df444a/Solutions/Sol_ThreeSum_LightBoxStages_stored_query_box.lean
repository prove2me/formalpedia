-- Prove2me | solution 1 for ThreeSum.LightBoxStages.stored_query_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:33.184629+00:00
-- url     : https://prove2.me/submissions/4384c4fc-727a-4eeb-9030-4f8a2384a1d7

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_ThreeSum_BoxStages_query_box_stage


set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxStages
theorem _root_.solution {μ : ℕ → ℤ} {L cut base : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L)
    (q u : Finset (Fin L)) (hu : u.Nonempty) (hflags : (q \ u).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) (u.min' hu).val+subsetRank (q \ u)) =
      SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight := by
  rw [h (u.min' hu).val (Nat.le_of_lt (u.min' hu).isLt) (q \ u) hflags]
  exact (query_box_stage weight q u hu).symm
end ThreeSum.LightBoxStages
