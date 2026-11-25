-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:24.550553+00:00
-- url     : https://prove2.me/submissions/a90a6e5a-06c6-4fda-8ca0-e26be6d7cfe8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Theorems.Thm_GroundTheory_GroupCoh_diagonalSuccIsoFree_inv_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by
  change (standardComplex.ε k G).hom ((diagonalSuccIsoFree k G 0).inv.hom
    (Finsupp.single v (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single]
  simp [standardComplex.ε]
end GroundTheory.GroupCoh
