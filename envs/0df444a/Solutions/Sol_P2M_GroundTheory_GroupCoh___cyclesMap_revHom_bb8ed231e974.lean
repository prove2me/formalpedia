-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:10:53.352501+00:00
-- url     : https://prove2.me/submissions/41da9359-f2dd-4a78-819c-189f0bd75b3d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Theorems.Thm_GroundTheory_GroupCoh_homologyMap_revHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A : Rep k G} {n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (z : cocycles A n) :
    π A n (HomologicalComplex.cyclesMap (revHom A) n z) = π A n z := by
  have h := congr(($(HomologicalComplex.homologyπ_naturality (revHom A) n)).hom z)
  rw [homologyMap_revHom, Category.comp_id] at h
  exact h.symm
end GroundTheory.GroupCoh
