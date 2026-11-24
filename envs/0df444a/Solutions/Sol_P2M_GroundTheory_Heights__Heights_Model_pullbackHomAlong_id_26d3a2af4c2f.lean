-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:43.142143+00:00
-- url     : https://prove2.me/submissions/fddf329a-8ced-4ff3-be7b-02aa7967acf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom

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
open CategoryTheory AlgebraicGeometry
noncomputable section
variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (e : g ≫ h = k) (F : Z.Modules) :
    pullbackHomAlong e (𝟙 ((Scheme.Modules.pullback h).obj F)) = 𝟙 _ := by
  simp [pullbackHomAlong]
end GroundTheory.Heights₂.Heights.Model
