-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.874846+00:00
-- url     : https://prove2.me/submissions/8e53f602-3679-4e46-a9a5-3c578da314da

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
theorem _root_.solution (e : g ≫ h = k) {F G H : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G)
    (ψ' : (Scheme.Modules.pullback h).obj G ⟶ (Scheme.Modules.pullback h).obj H) :
    pullbackHomAlong e (ψ ≫ ψ') = pullbackHomAlong e ψ ≫ pullbackHomAlong e ψ' := by
  simp [pullbackHomAlong]
end GroundTheory.Heights₂.Heights.Model
