-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB.hasFDerivAt_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:27.350308+00:00
-- url     : https://prove2.me/submissions/fd929ba5-98c8-409f-8a03-92e6ef296567

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_mop_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_continuous_mop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H] [FiniteDimensional ℂ H]
  {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
  (ν : Measure K) [IsFiniteMeasure ν]
  (c : K → H →L[ℂ] H) (hc : Continuous c) {U Ω : Set H} (hU : IsOpen U) (hΩ : IsOpen Ω)
  (hUΩ : ∀ x ∈ U, ∀ k, c k x ∈ Ω)
include hc hU hΩ hUΩ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
theorem _root_.solution {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E) (hf : ContDiffOn ℂ 1 f Ω)
    (hL : Continuous L) {x₀ : H} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ k, L k (f (c k x)) ∂ν)
      (∫ k, Mop c L k (fderiv ℂ f (c k x₀)) ∂ν) x₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hSU : Metric.closedBall x₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hfc : ContinuousOn f Ω := hf.continuousOn
  have hfd : ContinuousOn (fderiv ℂ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hdiff : ∀ y ∈ Ω, DifferentiableAt ℂ f y := fun y hy =>
    (hf.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hy)
  have hcont : ∀ x ∈ U, Continuous fun k => L k (f (c k x)) := fun x hx =>
    hL.clm_apply (hfc.comp_continuous (hc.clm_apply continuous_const) fun k => hUΩ x hx k)
  have hcont' : Continuous fun k => Mop c L k (fderiv ℂ f (c k x₀)) :=
    (continuous_mop c hc hL).clm_apply
      (hfd.comp_continuous (hc.clm_apply continuous_const) fun k => hUΩ x₀ hx₀ k)
  have hcj : Continuous fun p : K × H => c p.1 p.2 := (hc.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn
    (f := fun p : K × H => Mop c L p.1 (fderiv ℂ f (c p.1 p.2)))
    (((continuous_mop c hc hL).comp continuous_fst).continuousOn.clm_apply
      (hfd.comp hcj.continuousOn fun p hp => hUΩ p.2 (hSU hp.2) p.1))
  have hI : Integrable (fun k => L k (f (c k x₀))) ν := by
    obtain ⟨C0, hC0⟩ := (isCompact_range (hcont x₀ hx₀)).isBounded.exists_norm_le
    exact Integrable.of_bound (hcont x₀ hx₀).aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun k => hC0 _ (Set.mem_range_self k))
  have hD : ∀ k, ∀ x ∈ U,
      HasFDerivAt (fun x => L k (f (c k x))) (Mop c L k (fderiv ℂ f (c k x))) x := by
    intro k x hx
    rw [mop_apply]
    exact (L k).hasFDerivAt.comp x ((hdiff _ (hUΩ x hx k)).hasFDerivAt.comp x (c k).hasFDerivAt)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (bound := fun _ => C)
    (F := fun x k => L k (f (c k x))) (F' := fun x k => Mop c L k (fderiv ℂ f (c k x)))
    (Metric.ball_mem_nhds x₀ (half_pos hε))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ (half_pos hε)) fun x hx =>
      (hcont x (hSU (Metric.ball_subset_closedBall hx))).aestronglyMeasurable)
    hI hcont'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k x hx =>
      hC (k, x) ⟨Set.mem_univ _, Metric.ball_subset_closedBall hx⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k x hx => hD k x (hSU (Metric.ball_subset_closedBall hx)))
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
