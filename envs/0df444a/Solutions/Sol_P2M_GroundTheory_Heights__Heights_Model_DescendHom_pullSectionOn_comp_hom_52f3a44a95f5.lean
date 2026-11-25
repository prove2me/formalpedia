-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:01.577564+00:00
-- url     : https://prove2.me/submissions/22b4afb5-042e-4dca-8713-8296fa955dfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d

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
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model.DescendHom
theorem _root_.solution (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).hom.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m)) = pullSectionOn (f ≫ h) M O m := by
  rw [← pullSectionOn_comp_inv, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app]
  rfl
end GroundTheory.Heights₂.Heights.Model.DescendHom
