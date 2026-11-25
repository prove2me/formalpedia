-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:11.965011+00:00
-- url     : https://prove2.me/submissions/c595254b-3bee-4b6d-b0c4-af4e94e37bfb

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
theorem _root_.solution (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : U ⟶ V) :
    Function.Injective (M.presheaf.map i.op) := by
  have : i = eqToHom h := Subsingleton.elim _ _
  subst this
  exact (ConcreteCategory.bijective_of_isIso _).1
end GroundTheory.Heights₂.Heights.Model.DescendHom
