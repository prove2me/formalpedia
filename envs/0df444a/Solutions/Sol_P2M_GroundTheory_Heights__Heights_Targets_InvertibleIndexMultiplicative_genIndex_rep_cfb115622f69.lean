-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_genIndex_rep_cfb115622f69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:31.822372+00:00
-- url     : https://prove2.me/submissions/18fc1d3e-d365-4c2f-ba24-25e9bfb0dfd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
theorem _root_.solution [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : Ω) ≠ 0 := fun h => hδ (Subtype.ext h)
  have g := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := X) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hX x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact index_ne_zero hI)
    (relIndex_mulBy_ne_zero hδ)
  rwa [relIndex_map_subtype] at g
end GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
