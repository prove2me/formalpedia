-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.adj_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:54.221039+00:00
-- url     : https://prove2.me/submissions/1451f156-4520-4370-830c-4d7fdbbfad0d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (b : Fin n → ℂ) :
    ∑ j, M.adjugate k j * b j = (M.updateCol k b).det := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct]
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
