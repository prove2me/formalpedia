-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:33.256676+00:00
-- url     : https://prove2.me/submissions/f9140a29-e52b-4644-9367-45ba7d3b8dbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
theorem _root_.solution {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by
  intro hI
  obtain ⟨⟨x, hxX⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hX0
  obtain ⟨y, hy, hxy⟩ := (hX x).1 hxX
  rw [hI, Ideal.mem_bot] at hy
  subst hy
  have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  simp [hβL, hx] at hxy
end GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
