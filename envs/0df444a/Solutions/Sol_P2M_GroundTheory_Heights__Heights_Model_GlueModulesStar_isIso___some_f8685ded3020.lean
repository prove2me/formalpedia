-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:54.147701+00:00
-- url     : https://prove2.me/submissions/8b244c21-8aff-40fb-9e6e-aee65018ec9f

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
theorem _root_.solution [DecidableEq ι] {I : MulticospanIndex (starShape ι) C} {K : Multifork I}
    (hK : IsLimit K) (i : ι) (hi : IsIso (I.fst i)) (h : ∀ j, j ≠ i → IsIso (I.snd j)) :
    IsIso (K.ι (some i)) := by
  let s₀ : I.left (some i) ⟶ I.left none := I.snd i ≫ @inv _ _ _ _ (I.fst i) hi
  let k : ∀ a, I.left (some i) ⟶ I.left a := fun a => match a with
    | none => s₀
    | some j => if hj : j = i then eqToHom (by rw [hj]) else
        haveI := h j hj; s₀ ≫ I.fst j ≫ inv (I.snd j)
  have hk : ∀ b, k ((starShape ι).fst b) ≫ I.fst b = k ((starShape ι).snd b) ≫ I.snd b := by
    intro b
    by_cases hb : b = i
    · subst hb; simp [k, s₀]
    · simp [k, hb]
  have h0 : K.ι (some i) ≫ s₀ = K.ι none := by
    have hc := K.condition i
    dsimp at hc
    simp [s₀, ← reassoc_of% hc]
  refine ⟨⟨Multifork.IsLimit.lift hK k hk, ?_, ?_⟩⟩
  · apply Multifork.IsLimit.hom_ext hK
    rintro (_ | j)
    · simpa [k] using h0
    · by_cases hj : j = i
      · subst hj; simp [k]
      · have := h j hj
        have hc := K.condition j
        dsimp at hc
        simp only [Category.assoc, Multifork.IsLimit.fac, Category.id_comp, k, dif_neg hj]
        rw [reassoc_of% h0, reassoc_of% hc, IsIso.hom_inv_id, Category.comp_id]
  · simp [k]
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar
