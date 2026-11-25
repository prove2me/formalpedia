-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.weight_nsmul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:21:40.74688+00:00
-- url     : https://prove2.me/submissions/54115a76-2073-4745-a372-da69abd4185c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_weight_zero_eq_zero

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
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by
  induction m with
  | zero => rw [zero_nsmul, weight_zero_eq_zero A i y hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring
end ReciprocityTheory.L2DbarEstimates.Y
