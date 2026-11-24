-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:20.746648+00:00
-- url     : https://prove2.me/submissions/ea73347d-e50c-4807-a10a-503c681f1610

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom

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
    ((Scheme.Modules.pullbackComp f h).inv.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn (f ≫ h) M O m) =
        pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m) := by
  have hu := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction h).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ h)) (Scheme.Modules.pullbackComp f h).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom m) hu
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm
end GroundTheory.Heights₂.Heights.Model.DescendHom
