-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fc_wdb_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:10.049927+00:00
-- url     : https://prove2.me/submissions/5b758450-d3ba-411a-bd7f-abc2816e0e5d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n : ℕ) (p : V n → ℂ) (v : V n) (hp : DifferentiableAt ℂ p v) (j : Fin n) :
    wdb n j p v = 0 := by
  unfold wdb
  rw [hp.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ p v (bas n j) / 2) * Complex.I_mul_I
end ReciprocityTheory.L2DbarEstimates.Y
