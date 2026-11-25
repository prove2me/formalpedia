-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inr_inl_33cc3b99f307
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:43.331449+00:00
-- url     : https://prove2.me/submissions/9d736a8f-61af-41fd-b1e2-b7ccbfa83811

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K K₂ M : Type*} [Zero M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
theorem _root_.solution (f : K₂ → M) (k : K) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inl k) = 0 := by
  rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
  rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
