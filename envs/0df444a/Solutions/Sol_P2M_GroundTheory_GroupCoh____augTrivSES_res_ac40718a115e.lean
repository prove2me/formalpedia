-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh____augTrivSES_res_ac40718a115e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:06:57.246713+00:00
-- url     : https://prove2.me/submissions/fe919373-f3ea-4cba-91c2-b2c6191bd608

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
variable {k G}
variable (k) {H : Type u} [Group H] (φ : H →* G)
namespace GroundTheory.GroupCoh
theorem _root_.solution :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by
  have hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) =
      d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k)) := by
    funext h
    change MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  exact δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ)
    (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx
end GroundTheory.GroupCoh
