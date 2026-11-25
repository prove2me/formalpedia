-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:04.1798+00:00
-- url     : https://prove2.me/submissions/95a1bcfe-4de2-4df8-9fee-24287a83c486

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {m : WithTop ℕ∞}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContDiffOn ℝ m (F i j) S) (k l : Fin n) :
    ContDiffOn ℝ m (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by
  simp only [Matrix.adjugate_apply]
  refine cdo_det (F := fun i j w => ((Matrix.of fun i j => F i j w).updateRow l (Pi.single k 1)) i j)
    fun i j => ?_
  by_cases h : i = l
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte, Matrix.of_apply]
    exact hF i j
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
