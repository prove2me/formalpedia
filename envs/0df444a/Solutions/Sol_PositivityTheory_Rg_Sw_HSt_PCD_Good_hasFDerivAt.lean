-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.PCD.Good.hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:41.036088+00:00
-- url     : https://prove2.me/submissions/6b171e7e-795a-4983-8f54-3883de96ad15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_continuousOn
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_dK
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_PCD_Good_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
namespace PositivityTheory.Rg.Sw.HSt.PCD
namespace Good
theorem _root_.solution [CompleteSpace E] (hΩ : IsOpen Ω) (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {x₀ : F} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, K x u ∂ν) (∫ u, fderiv ℝ (K · u) x₀ ∂ν) x₀ := by
  obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hΩ.inter hV) x₀ ⟨hx₀, hxV⟩
  have hK' := hK.dK hΩ
  have hc' := hK'.continuousOn
  have hcb : IsCompact (Metric.closedBall x₀ (ε / 2) ×ˢ C) := (isCompact_closedBall _ _).prod hC
  have hsub : Metric.closedBall x₀ (ε / 2) ×ˢ C ⊆ Ω ×ˢ univ := by
    intro p hp
    exact ⟨(hεs (Metric.closedBall_subset_ball (by linarith) hp.1)).1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcb.exists_bound_of_continuousOn (hc'.mono hsub)
  have hcont_u : ∀ x ∈ Ω, Continuous (K x) := fun x hx =>
    hK.continuousOn.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hcont'_u : ∀ x ∈ Ω, Continuous (fun u => fderiv ℝ (K · u) x) := fun x hx =>
    hc'.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hball : Metric.ball x₀ (ε / 2) ⊆ Ω ∩ V := fun y hy => hεs (Metric.ball_subset_ball (by linarith) hy)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := K) (F' := fun x u => fderiv ℝ (K · u) x)
    (s := Metric.ball x₀ (ε / 2))
    (bound := C.indicator fun _ => M) (Metric.ball_mem_nhds _ (by linarith)) ?_ (hK.integrable ν hx₀)
    (hcont'_u x₀ hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx using (hcont_u x hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    by_cases hu : u ∈ C
    · rw [indicator_of_mem hu]
      exact hM (x, u) ⟨Metric.ball_subset_closedBall hx, hu⟩
    · rw [indicator_of_notMem hu]
      have : (K · u) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hV.mem_nhds (hball hx).2] with y hy using hKV y hy u hu
      rw [this.fderiv_eq]
      simp
  · exact (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hC.isClosed.measurableSet
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    have hxΩ := (hball hx).1
    exact ((hK.smooth u).differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ) |>.hasFDerivAt
end Good
end PositivityTheory.Rg.Sw.HSt.PCD
