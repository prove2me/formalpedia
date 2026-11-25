-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_nsq_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:35.401797+00:00
-- url     : https://prove2.me/submissions/c712d629-bc10-472d-b229-63fdc2ddf07f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA

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
theorem _root_.solution {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i : ι} {y : Y}
    (hy : y ∈ U) (hi : y ∈ (A.chart i).source) :
    A.nsq la a y = ‖a i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold bsTr at ha
  unfold WeightedAtlas.nsq
  have hg : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne la (A.pick y) i y hp hi)) 2
  rw [ha (A.pick y) i y hy hp hi, A.ph_trans la (A.pick y) i y hp hi, norm_mul, mul_pow, neg_sub,
    sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
