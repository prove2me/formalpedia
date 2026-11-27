-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_mem_sympGroup_964162e978e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:33.680971+00:00
-- url     : https://prove2.me/submissions/8fa8de3c-ab89-4fe1-997b-bf90695a0b8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_WeilPolarization_WmSysObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Matrix
set_option linter.unusedSectionVars false
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution {ω : LinearMap.BilinForm R W} {g : W ≃ₗ[R] W} :
    g ∈ sympGroup ω ↔ ∀ w w', ω (g w) (g w') = ω w w' := Iff.rfl
end GroundTheory.Heights₂.Theta
