-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:55.925714+00:00
-- url     : https://prove2.me/submissions/4ceb4d4c-1072-45df-b82e-f6947bd6eca0

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
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {m : WithTop ℕ∞}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContDiffOn ℝ m (F i j) S) :
    ContDiffOn ℝ m (fun w => (Matrix.of fun i j => F i j w).det) S := by
  simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hF _ _
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
