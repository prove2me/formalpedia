-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_proof_f81e5bcc8a64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:49.335806+00:00
-- url     : https://prove2.me/submissions/1ce07c24-114b-4a75-a805-6bd1875fd514

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace DescendHom
theorem _root_.solution : DescendHom.Statement := by
  intro T Y Z ι _ g' g e F G φ hinj hex
  subst e
  choose t ht using hex
  refine ⟨DescendHom.descendPsi ι g' φ hinj t ht, ?_⟩
  have hR : (g' ≫ ι) ⁻¹ᵁ ι.opensRange = ⊤ := top_le_iff.1 fun x _ => ⟨g'.base x, rfl⟩
  refine DescendHom.hom_eq_of_pullSectionOn (g' ≫ ι) ι.opensRange hR _ _ fun V hV s => ?_
  rw [DescendHom.pullbackHomAlong_rfl]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [DescendHom.pullSectionOn_comp_inv]
  erw [DescendHom.pullSectionOn_naturality g' _ (ι ⁻¹ᵁ V), DescendHom.descendPsi_pull ι g' φ hinj t ht V hV s]
  rw [DescendHom.pullSectionOn_comp_hom, ht]
end DescendHom
end GroundTheory.Heights₂.Heights.Model
