-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:44.152824+00:00
-- url     : https://prove2.me/submissions/c8391dab-3f94-49bc-b522-548406ae0dd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt.mulBy_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
theorem _root_.solution [NumberField L] {B : Subring L} [Module.Finite ℤ B] (β : B) :
    (1 : Submodule (𝓞 L) L).toAddSubgroup.map (mulBy (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B))).toAddSubgroup := by
  have hspan : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B)) =
      Submodule.span (𝓞 L) {(β : L)} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      show (c : L) * (β : L) ∈ _
      exact mul_mem_of_mem c.2 (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨β, Ideal.mem_span_singleton_self β, rfl⟩
  rw [hspan]
  ext x
  simp only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup, Submodule.mem_one,
    Submodule.mem_span_singleton, Algebra.smul_def]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, mul_comm _ _⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, mul_comm _ _⟩
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
