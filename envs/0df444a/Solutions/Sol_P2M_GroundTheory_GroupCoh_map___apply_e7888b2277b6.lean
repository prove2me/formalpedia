-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:44.956817+00:00
-- url     : https://prove2.me/submissions/32621ee1-21fa-473b-8a2c-8111361b0609

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_TateCohomology_CupProduct

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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    map (MonoidHom.id G) φ n (π A n z) = π A' n (cocyclesMap (MonoidHom.id G) φ n z) := by
  change (π A n ≫ map (MonoidHom.id G) φ n).hom z =
    (cocyclesMap (MonoidHom.id G) φ n ≫ π A' n).hom z
  rw [π_map]
end GroundTheory.GroupCoh
