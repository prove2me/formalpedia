-- Prove2me | solution 1 for ThreeSum.LightZetaStages.stored_forced_lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:05.908193+00:00
-- url     : https://prove2.me/submissions/3c07a11a-5261-4fce-991f-c29a780fd696

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_forced_prefix


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaStages
theorem _root_.solution {μ : ℕ → ℤ} {L cut base j : ℕ}
    {f : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut f L) (hj : j ≤ L)
    (pre tail : Finset (Fin L)) (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j)
    (hcut : (pre ∪ tail).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank (pre ∪ tail)) =
      ∑ x ∈ tail.powerset, f (pre ∪ x) := by
  rw [h j hj (pre ∪ tail) hcut]
  exact stageValue_forced_prefix f j pre tail hp ht
end ThreeSum.LightZetaStages
