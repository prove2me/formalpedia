-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_nsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:50.372686+00:00
-- url     : https://prove2.me/submissions/4c4024d4-6050-464a-9db0-3dc4eaf90b65

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_eq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuousOn_sec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuousOn_ph

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
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) :
    Continuous (A.nsq la s) := by
  rw [continuous_iff_continuousAt]
  intro y
  set i := A.pick y
  have hU : (A.chart i).source ∈ 𝓝 y := (A.chart i).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun x => ‖s i x‖ ^ 2 * Real.exp (-A.ph la i x)) (A.chart i).source :=
    ((A.continuousOn_sec hs i).norm.pow 2).mul ((A.continuousOn_ph la i).neg.rexp)
  refine (hc.continuousAt hU).congr ?_
  filter_upwards [hU] with x hx
  exact (A.nsq_eq_chart hs hx).symm
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
