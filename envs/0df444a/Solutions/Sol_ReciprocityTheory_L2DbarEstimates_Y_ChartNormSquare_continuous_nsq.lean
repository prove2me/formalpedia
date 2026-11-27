-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.continuous_nsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:24.765246+00:00
-- url     : https://prove2.me/submissions/883fc6c1-bef5-468d-98b6-84bbada3f462

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_continuousOn_source_of
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_nsq_eq_chart

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
open ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ)
    (hF : A.IsSec la F) : Continuous (A.nsq la F) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hFc : ContinuousOn (F (A.pick y)) (A.chart (A.pick y)).source := by
    apply continuousOn_source_of
    have := (hF.1 (A.pick y)).continuousOn
    simpa using this
  have hph : ContinuousOn (A.ph la (A.pick y)) (A.chart (A.pick y)).source :=
    continuousOn_source_of _ _ ((A.smooth_ph la (A.pick y)).continuousOn)
  have hc : ContinuousOn (fun x => ‖F (A.pick y) x‖ ^ 2 * Real.exp (-A.ph la (A.pick y) x))
      (A.chart (A.pick y)).source :=
    (hFc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with x hx
  exact (nsq_eq_chart A la F hF _ x hx).symm
end ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
