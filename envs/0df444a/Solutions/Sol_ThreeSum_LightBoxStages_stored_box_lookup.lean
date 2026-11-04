-- Prove2me | solution 1 for ThreeSum.LightBoxStages.stored_box_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:54.159876+00:00
-- url     : https://prove2.me/submissions/f2894473-bf8c-4588-9c4a-a88ca0f30f6a

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_ThreeSum_BoxStages_stageValue_eq_boxSum


set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxStages
theorem _root_.solution {μ : ℕ → ℤ} {L cut base j : ℕ}
    {weight : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut weight L) (hj : j ≤ L)
    (flags : Finset (Fin L)) (hflags : flags.card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank flags) =
      SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight := by
  rw [h j hj flags hflags]
  exact stageValue_eq_boxSum weight j flags
end ThreeSum.LightBoxStages
