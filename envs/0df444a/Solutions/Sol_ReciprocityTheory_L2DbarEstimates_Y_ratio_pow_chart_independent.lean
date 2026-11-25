-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ratio_pow_chart_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:36.474113+00:00
-- url     : https://prove2.me/submissions/ff6e7ad1-d9b8-400b-833d-3755cd9e3e8d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_transition_nsmul_eq_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (F w0 : ι → Y → ℂ)
    (hF : A.IsSec (m • la) F) (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    F i y / w0 i y ^ m = F j y / w0 j y ^ m := by
  rw [hF.2 i j y (Set.mem_univ y) hi hj, hw.2 i j y (Set.mem_univ y) hi hj,
    transition_nsmul_eq_pow A la m i j y hi hj, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (A.g_ne la i j y hi hj))
end ReciprocityTheory.L2DbarEstimates.Y
