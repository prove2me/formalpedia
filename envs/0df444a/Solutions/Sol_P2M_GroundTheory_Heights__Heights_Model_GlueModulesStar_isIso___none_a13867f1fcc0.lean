-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_a13867f1fcc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:51.504231+00:00
-- url     : https://prove2.me/submissions/606335ea-aa4a-43bb-832f-e71290711662

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
variable {C : Type*} [Category C] {ι : Type*}
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution {I : MulticospanIndex (starShape ι) C} {K : Multifork I} (hK : IsLimit K)
    (h : ∀ j, IsIso (I.snd j)) : IsIso (K.ι none) := by
  let k : ∀ a, I.left none ⟶ I.left a := fun a => match a with
    | none => 𝟙 _
    | some j => haveI := h j; I.fst j ≫ inv (I.snd j)
  have hk : ∀ b, k ((starShape ι).fst b) ≫ I.fst b = k ((starShape ι).snd b) ≫ I.snd b := by
    intro b; simp [k]
  refine ⟨⟨Multifork.IsLimit.lift hK k hk, ?_, ?_⟩⟩
  · apply Multifork.IsLimit.hom_ext hK
    rintro (_ | j)
    · simp [k]
    · have hc := K.condition j
      dsimp at hc
      simp [k, reassoc_of% hc]
  · simp [k]
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar
