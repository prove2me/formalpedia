-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.SmoothIntegrals.hasFDerivAt_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:08.726806+00:00
-- url     : https://prove2.me/submissions/29ec20a9-5ecb-429b-a80f-3fe1ce077630

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_pd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}
namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals
theorem _root_.solution (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0)
    {x₀ : X} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ y, Q (x, p y) ∂μ) (∫ y, pd Q (x₀, p y) ∂μ) x₀ := by
  obtain ⟨K, hK, hKe⟩ := hs x₀ hx₀
  have hUW := hU.prod hW
  obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff_ball.1 hKe
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set ε := min (δ / 2) (ε₀ / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos hε₀)
  have hcb : closedBall x₀ ε ⊆ U := fun x hx =>
    hε₀U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀))))
  have hcbδ : closedBall x₀ ε ⊆ ball x₀ δ := fun x hx =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)))
  have hQc : ContinuousOn Q (U ×ˢ W) := hQ.continuousOn
  have hPc : ContinuousOn (pd Q) (U ×ˢ W) := (contDiffOn_pd hU hW hQ).continuousOn
  have hcpt : IsCompact (closedBall x₀ ε ×ˢ (p '' K)) := (isCompact_closedBall x₀ ε).prod (hK.image hp)
  have hsub : closedBall x₀ ε ×ˢ (p '' K) ⊆ U ×ˢ W := prod_mono hcb (by rintro _ ⟨y, -, rfl⟩; exact hpW y)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hPc.mono hsub)
  have hzero : ∀ x ∈ ball x₀ δ, ∀ y ∉ K, pd Q (x, p y) = 0 := by
    intro x hx y hy
    have h0 : (fun x' => Q (x', p y)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with x' hx' using hδK x' hx' y hy
    show fderiv ℝ (fun x' => Q (x', p y)) x = 0
    rw [h0.fderiv_eq]
    exact fderiv_const_apply _
  have hdiff : ∀ x ∈ U, ∀ y, HasFDerivAt (fun x' => Q (x', p y)) (pd Q (x, p y)) x := by
    intro x hx y
    have h1 : ContDiffAt ℝ ∞ Q (x, p y) := hQ.contDiffAt (hUW.mem_nhds ⟨hx, hpW y⟩)
    have h2 : DifferentiableAt ℝ (fun x' => Q (x', p y)) x :=
      (h1.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))
    exact h2.hasFDerivAt
  have hcont : ∀ x ∈ U, Continuous fun y => Q (x, p y) := fun x hx =>
    hQc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  have hcont' : ∀ x ∈ U, Continuous fun y => pd Q (x, p y) := fun x hx =>
    hPc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (F := fun x y => Q (x, p y))
    (F' := fun x y => pd Q (x, p y)) (s := ball x₀ ε) (bound := K.indicator fun _ => C)
    (ball_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hU.mem_nhds hx₀] with x hx using (hcont x hx).aestronglyMeasurable
  · exact (hcont x₀ hx₀).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy => hδK x₀ (mem_ball_self hδ) y hy)
  · exact (hcont' x₀ hx₀).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact hC _ ⟨ball_subset_closedBall hx, mem_image_of_mem p hy⟩
    · rw [hzero x (hcbδ (ball_subset_closedBall hx)) y hy, indicator_of_notMem hy, norm_zero]
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · exact ae_of_all _ fun y x hx => hdiff x (hcb (ball_subset_closedBall hx)) y
end PositivityTheory.Rg.BcB.CG.SmoothIntegrals
