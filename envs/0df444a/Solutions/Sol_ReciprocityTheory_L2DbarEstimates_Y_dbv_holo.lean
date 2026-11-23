-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.dbv_holo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:36.06824+00:00
-- url     : https://prove2.me/submissions/50dc6849-d501-4e33-ba5a-d9fe80d5eedb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {G : V n → ℂ} {v : V n} (hG : DifferentiableAt ℂ G v) (ζ : V n) :
    dbv (fderiv ℝ G v) ζ = 0 := by
  unfold dbv
  rw [hG.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, ← mul_assoc, I_mul_I]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
