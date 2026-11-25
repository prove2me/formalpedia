-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_map___apply__b45ef1ec43d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:40.92126+00:00
-- url     : https://prove2.me/submissions/80606656-2111-44a6-8e60-7df9fa999de3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupFunctorial

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
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]
end GroundTheory.GroupCoh
