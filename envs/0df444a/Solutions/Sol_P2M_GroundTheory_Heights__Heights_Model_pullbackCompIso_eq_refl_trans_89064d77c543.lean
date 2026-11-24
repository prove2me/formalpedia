-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_eq_refl_trans_89064d77c543
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.280376+00:00
-- url     : https://prove2.me/submissions/91d5810b-4f68-4866-a4ef-62ad7d7199c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackCompIso_trans_right_2820c52d5ef0

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
theorem _root_.solution {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    pullbackCompIso e γ = pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso γ := by
  rw [← pullbackCompIso_trans_right, Iso.refl_trans]
end GroundTheory.Heights₂.Heights.Model
