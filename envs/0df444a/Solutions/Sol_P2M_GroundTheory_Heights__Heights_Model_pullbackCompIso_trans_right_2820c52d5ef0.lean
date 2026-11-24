-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.25791+00:00
-- url     : https://prove2.me/submissions/ea75c291-b359-4481-8b4c-dbf652daea81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence

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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F F' : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) (δ : F ≅ F') :
    pullbackCompIso e (γ ≪≫ δ) = pullbackCompIso e γ ≪≫ (Scheme.Modules.pullback g).mapIso δ := by
  ext1
  simp [pullbackCompIso]
end GroundTheory.Heights₂.Heights.Model
