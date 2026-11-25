-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_map_H1__augCocycle_051c44b13fd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:25.992708+00:00
-- url     : https://prove2.me/submissions/5f4c9302-3a13-4b92-9713-1c7b4e8a2bc9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Theorems.Thm_GroundTheory_GroupCoh_cocycleHom_augIdealSubOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1
  apply cocycles₁_ext
  intro h
  exact cocycleHom_augIdealSubOne f (φ h)
end GroundTheory.GroupCoh
