-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:31.788162+00:00
-- url     : https://prove2.me/submissions/8533ef56-72b6-40a0-aca7-0da66f87d50c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {g₁ g₂ : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e₁ : g₁ ≫ h = k) (e₂ : g₂ ≫ h = k)
    (hg : g₁ = g₂)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e₁ ψ = along e₂ ψ := by
  subst hg; rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
