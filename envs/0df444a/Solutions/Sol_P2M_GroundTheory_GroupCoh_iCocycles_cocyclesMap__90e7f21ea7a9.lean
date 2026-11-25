-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_iCocycles_cocyclesMap__90e7f21ea7a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:35.346879+00:00
-- url     : https://prove2.me/submissions/2e4ef3a1-988c-4d89-8c54-8b43ddb6d920

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
theorem _root_.solution {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl
end GroundTheory.GroupCoh
