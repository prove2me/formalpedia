-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.transition_nsmul_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:00.112938+00:00
-- url     : https://prove2.me/submissions/144ea66b-d079-4822-8c4a-36d46a1de823

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_transition_zero_eq_one

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
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, transition_zero_eq_one A i j y hi hj]
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]
end ReciprocityTheory.L2DbarEstimates.Y
