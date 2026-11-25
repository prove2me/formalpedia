-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_nsq_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:33.481071+00:00
-- url     : https://prove2.me/submissions/a921b8db-3d32-4bbb-ac1f-5c74d04dfedc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_tr_of_isSecOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_continuousOn_section_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ph_cont
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


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
theorem _root_.solution {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) : Continuous (A.nsq la a) := by
  have htr : bsTr A la Set.univ a := bsA_tr_of_isSecOn A (U := Set.univ) ha
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun z => ‖a (A.pick y) z‖ ^ 2 * Real.exp (-A.ph la (A.pick y) z))
      (A.chart (A.pick y)).source :=
    ((continuousOn_section_chart A ha (A.pick y)).norm.pow 2).mul ((bsA_ph_cont A la (A.pick y)).neg.rexp)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with z hz
  exact (bsA_nsq_chart A htr (Set.mem_univ z) hz).symm
end ReciprocityTheory.L2DbarEstimates.Y
