-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FlatBC_subEquiv_one_tmul_19804f52a53f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:40.7628+00:00
-- url     : https://prove2.me/submissions/8ebfaa4e-bacb-482f-b493-1ae154345897

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open TensorProduct MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.FlatBC
variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']
variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']
variable [Module.Flat S S']
namespace GroundTheory.Heights₂.Heights.Kleiman.FlatBC
theorem _root_.solution (E : S' ⊗[S] X ≃ₗ[S'] X') (D : Submodule S X) (D' : Submodule S' X')
    (h₁ : ∀ x ∈ D, E (1 ⊗ₜ x) ∈ D')
    (h₂ : D' ≤ Submodule.span S' ((fun x => E (1 ⊗ₜ x)) '' (D : Set X))) (x : D) :
    (subEquiv E D D' h₁ h₂ (1 ⊗ₜ x) : X') = E (1 ⊗ₜ (x : X)) :=
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.FlatBC
