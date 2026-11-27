-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueTwo_proof_c459b7929b7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:35.706297+00:00
-- url     : https://prove2.me/submissions/d10418a0-00a5-4769-bdf1-ed8d6fb960a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueTwo_pullbackCompIso_symm_trans_e730dbaac3a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b


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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.Model.GlueTwo
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Heights₂.Heights.Model.GlueTwo
theorem _root_.solution : GlueTwo.Statement := by
  intro X O₁ O₂ O O₁₂ h₁ h₂ _ k₁ k₂ hk F₁ F₂ ψ
  obtain rfl : O₁ ⊓ O₂ = O₁₂ := le_antisymm hk (le_inf k₁ k₂)
  let I := GlueModulesStar.index O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
  have h0 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)) :=
    GlueModulesStar.isIso_homEquiv_symm O₂.ι _ (fun W =>
      GlueModulesStar.isIso_ι_none_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ) _
        (O₂.ι_image_le W))
  have hi : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some ()))) :=
    GlueModulesStar.isIso_homEquiv_symm O₁.ι _ (fun W =>
      GlueModulesStar.isIso_ι_some_app O₂ (fun _ : Unit => O₁) F₂ (fun _ => F₁) (fun _ => ψ)
        (fun i j hij => absurd (Subsingleton.elim i j) hij) () _ (O₁.ι_image_le W))
  let a₂ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₂.ι).homEquiv _ _).symm
    (Multiequalizer.ι I none))
  let a₁ := asIso (((Scheme.Modules.pullbackPushforwardAdjunction O₁.ι).homEquiv _ _).symm
    (Multiequalizer.ι I (some ())))
  have hc : pullbackCompIso (X.homOfLE_ι k₂) a₂ = pullbackCompIso (X.homOfLE_ι k₁) a₁ ≪≫ ψ := by
    ext1
    apply ((Scheme.Modules.pullbackPushforwardAdjunction (O₁ ⊓ O₂).ι).homEquiv _ _).injective
    have e1 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₂) a₂ (𝟙 _)
    have e2 := GlueModulesStar.homEquiv_pullbackCompIso (X.homOfLE_ι k₁) a₁ ψ.hom
    rw [Category.comp_id] at e1
    rw [Iso.trans_hom, e1, e2]
    simp only [a₁, a₂, asIso_hom, Equiv.apply_symm_apply]
    exact Multiequalizer.condition I ()
  refine ⟨(Scheme.Modules.pullback O.ι).obj (multiequalizer I),
    (pullbackCompIso (X.homOfLE_ι h₁) (Iso.refl _)).symm ≪≫ a₁,
    (pullbackCompIso (X.homOfLE_ι h₂) (Iso.refl _)).symm ≪≫ a₂, ?_⟩
  rw [pullbackCompIso_symm_trans (X.homOfLE_ι h₂) (X.homOfLE_homOfLE k₂ h₂) (X.homOfLE_ι k₂)
      (X.homOfLE_ι _),
    pullbackCompIso_symm_trans (X.homOfLE_ι h₁) (X.homOfLE_homOfLE k₁ h₁) (X.homOfLE_ι k₁)
      (X.homOfLE_ι _), hc, Iso.trans_assoc]
end GroundTheory.Heights₂.Heights.Model.GlueTwo
