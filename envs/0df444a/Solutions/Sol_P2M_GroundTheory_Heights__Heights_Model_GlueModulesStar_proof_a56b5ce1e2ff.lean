-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_proof_a56b5ce1e2ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:25:21.697805+00:00
-- url     : https://prove2.me/submissions/98633a6c-50a5-4c9e-8646-ce5fd6dd3695

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___none_app_a110bafbd1d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947

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
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution : GlueModulesStar.Statement := by
  intro X V ι U _ hUU G F ψ
  let I := index V U G F ψ
  have h0 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)) :=
    isIso_homEquiv_symm V.ι _ (fun O => isIso_ι_none_app V U G F ψ _ (V.ι_image_le O))
  have hi : ∀ i, IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i))) := fun i =>
    isIso_homEquiv_symm (U i).ι _
      (fun O => isIso_ι_some_app V U G F ψ hUU i _ ((U i).ι_image_le O))
  refine ⟨multiequalizer I,
    asIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none)),
    fun i => asIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i))), fun i => ?_⟩
  ext1
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (U i ⊓ V).ι).homEquiv _ _).injective
  have h1 := homEquiv_pullbackCompIso (X.homOfLE_ι (inf_le_right : U i ⊓ V ≤ V))
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).symm
      (Multiequalizer.ι I none))) (𝟙 _)
  have h2 := homEquiv_pullbackCompIso (X.homOfLE_ι (inf_le_left : U i ⊓ V ≤ U i))
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction (U i).ι).homEquiv _ _).symm
      (Multiequalizer.ι I (some i)))) (ψ i).hom
  rw [Category.comp_id] at h1
  rw [Iso.trans_hom, h1, h2]
  simp only [asIso_hom, Equiv.apply_symm_apply]
  exact Multiequalizer.condition I i
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar
