-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:03.209446+00:00
-- url     : https://prove2.me/submissions/e74f53b8-972b-4ede-bb43-cab8a958926f

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
theorem _root_.solution (g : T ⟶ Y) {M N : Y.Modules} (χ : M ⟶ N) (V : Y.Opens)
    (m : Γ(M, V)) :
    ((Scheme.Modules.pullback g).map χ).app (g ⁻¹ᵁ V) (pullSectionOn g M V m) =
      pullSectionOn g N V (χ.app V m) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality χ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V).hom m) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.Model.DescendHom
