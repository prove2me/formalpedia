-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsC_nsq_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:58.596498+00:00
-- url     : https://prove2.me/submissions/6121f758-8630-4c67-85f0-d3f9ed0e4a2f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ph_cont


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
theorem _root_.solution {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : A.IsSecOn la U a)
    (hU : IsOpen U) : ContinuousOn (A.nsq la a) U := by
  intro y hy
  set i := A.pick y
  have hsrc : (A.chart i).source ∩ U ∈ 𝓝 y :=
    ((A.chart i).open_source.inter hU).mem_nhds ⟨A.mem_pick y, hy⟩
  have h1 : ContinuousOn (a i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (ha.1 i).continuousOn
  have h2 : ContinuousOn (a i) ((A.chart i).source ∩ U) := by
    have := h1.comp ((A.chart i).continuousOn.mono Set.inter_subset_left)
      (fun x (hx : x ∈ (A.chart i).source ∩ U) => ⟨(A.chart i).map_source hx.1, by simpa [(A.chart i).left_inv hx.1] using hx.2⟩)
    exact this.congr fun x hx => by simp [(A.chart i).left_inv hx.1]
  have hc : ContinuousAt (fun x => ‖a i x‖ ^ 2 * Real.exp (-A.ph la i x)) y := by
    have h3 := h2.continuousAt hsrc
    have h4 := (bsA_ph_cont A la i).continuousAt
      ((A.chart i).open_source.mem_nhds (A.mem_pick y))
    exact (h3.norm.pow 2).mul (h4.neg.rexp)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [hsrc] with x hx
  exact (bsA_nsq_chart A ha.2 hx.2 hx.1).symm
end ReciprocityTheory.L2DbarEstimates.Y
