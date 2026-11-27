-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ap_mu_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:06.304864+00:00
-- url     : https://prove2.me/submissions/027d2ad4-390c-486c-954f-32a778cda751

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeI

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
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (K : Set Y) (hK : IsCompact K) :
    A.mu K < ⊤ := by
  refine hK.measure_lt_top_of_nhdsWithin fun y _ => ?_
  set e := A.chart (A.pick y) with he
  have hys : y ∈ e.source := A.mem_pick y
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)
  have hδ : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2) := ⟨hys, Metric.mem_ball_self hδ⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩
  rw [A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]
  have himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Metric.ball_subset_closedBall hx.2
  have hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v)))
      (Metric.closedBall (e y) (ε / 2)) :=
    (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont
  calc _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) (e.symm v))) := lintegral_mono_set himg
    _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2), ENNReal.ofReal M := by
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro v hv
        apply ENNReal.ofReal_le_ofReal
        have h1 := hM v hv
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
        exact h1
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
end ReciprocityTheory.L2DbarEstimates.Y
