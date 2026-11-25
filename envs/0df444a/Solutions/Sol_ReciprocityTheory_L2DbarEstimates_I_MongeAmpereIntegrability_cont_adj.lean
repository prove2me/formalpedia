-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cont_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:57.149221+00:00
-- url     : https://prove2.me/submissions/b32bf5bd-5dc9-4938-8978-5ebcc7136261

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
theorem _root_.solution {X : Type*} [TopologicalSpace X] {S : Set X}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContinuousOn (F i j) S) (k l : Fin n) :
    ContinuousOn (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine continuousOn_finset_sum _ fun σ _ => continuousOn_const.mul ?_
  refine continuousOn_finset_prod _ fun i _ => ?_
  by_cases h : σ i = l
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte]
    exact continuousOn_const
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte, Matrix.of_apply]
    exact hF _ _
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
