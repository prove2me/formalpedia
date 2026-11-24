-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:43.696487+00:00
-- url     : https://prove2.me/submissions/a26e5965-58a2-4335-89a3-dd274d62b3a8

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
theorem _root_.solution (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (pullbackIsoAlong e ψ).hom = pullbackHomAlong e ψ.hom := by
  simp [pullbackIsoAlong, pullbackHomAlong]
end GroundTheory.Heights₂.Heights.Model
