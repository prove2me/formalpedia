-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_nsq_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:00.827076+00:00
-- url     : https://prove2.me/submissions/c3c358dc-589d-4924-b563-94648d50adef

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
theorem _root_.solution {la : La} {a : ι → Y → ℂ} {y : Y} (h : a (A.pick y) y ≠ 0) :
    0 < A.nsq la a y := by
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.mpr h) 2) (Real.exp_pos _)
end ReciprocityTheory.L2DbarEstimates.Y
