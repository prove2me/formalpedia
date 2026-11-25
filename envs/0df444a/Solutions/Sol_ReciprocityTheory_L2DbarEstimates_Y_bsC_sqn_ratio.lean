-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsC_sqn_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:05.017308+00:00
-- url     : https://prove2.me/submissions/607dcb76-e20d-488e-b888-a2cbe2407ce9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {N : ℕ} (la : La) (u : Fin N → ι → Y → ℂ) (w0 : ι → Y → ℂ) (y : Y)
    (h0 : w0 (A.pick y) y ≠ 0) :
    A.sqn la u y = A.nsq la w0 y * ∑ k, ‖u k (A.pick y) y / w0 (A.pick y) y‖ ^ 2 := by
  unfold sqn nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ‖w0 (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [norm_div, div_pow]
  field_simp
end ReciprocityTheory.L2DbarEstimates.Y
