-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:20.05892+00:00
-- url     : https://prove2.me/submissions/24f6627f-8a42-403b-bbe9-209775ff58c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_circleIntegral_inv_smul_eq_123c7f3e4e62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
theorem _root_.solution {k : ℕ} {U : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hf : DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}))
    (hb : ∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0})))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) :
    ∃ W ∈ 𝓝 τ₀, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      ∀ τ ∈ W, τ ∈ U → g τ ≠ 0 → F τ = f τ := by
  have hO : IsOpen (U ∩ {t | g t ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  by_cases hg0 : g τ₀ ≠ 0
  · exact ⟨U ∩ {t | g t ≠ 0}, hO.mem_nhds ⟨hτ₀, hg0⟩, f, hf, fun _ _ _ _ => rfl⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU τ₀ hτ₀
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne (ball τ₀ (r / 2)) isOpen_ball
    ((ball_subset_ball (by linarith)).trans hrU) ⟨τ₀, mem_ball_self (by linarith)⟩
  set v : Fin k → ℂ := t₁ - τ₀ with hvdef
  have hv : ‖v‖ < r / 2 := by
    rw [hvdef, ← dist_eq_norm]
    exact ht₁
  have hline : ∀ τ ∈ ball τ₀ (r / 4), ∀ z : ℂ, ‖z‖ < 3 / 2 → τ + z • v ∈ U := by
    intro τ hτ z hz
    apply hrU
    rw [mem_ball, dist_eq_norm] at hτ ⊢
    have h1 : ‖τ + z • v - τ₀‖ ≤ ‖τ - τ₀‖ + ‖z‖ * ‖v‖ := by
      rw [← norm_smul]
      calc ‖τ + z • v - τ₀‖ = ‖(τ - τ₀) + z • v‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z‖ * ‖v‖ ≤ 3 / 2 * (r / 2) := mul_le_mul hz.le hv.le (norm_nonneg _) (by norm_num)
    linarith
  have hlined : ∀ (τ : Fin k → ℂ) (z : ℂ), DifferentiableAt ℂ (fun z : ℂ => τ + z • v) z := by
    intro τ z
    fun_prop
  have hgline : ∀ τ ∈ ball τ₀ (r / 4),
      DifferentiableOn ℂ (fun z : ℂ => g (τ + z • v)) (ball 0 (3 / 2)) := by
    intro τ hτ z hz
    have h1 : DifferentiableAt ℂ g (τ + z • v) :=
      hg.differentiableAt (hU.mem_nhds (hline τ hτ z (mem_ball_zero_iff.mp hz)))
    exact (h1.comp z (hlined τ z)).differentiableWithinAt
  have hτ₀b : τ₀ ∈ ball τ₀ (r / 4) := mem_ball_self (by linarith)
  have hφa : AnalyticOnNhd ℂ (fun z : ℂ => g (τ₀ + z • v)) (ball 0 (3 / 2)) :=
    (hgline τ₀ hτ₀b).analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := mem_ball_self (by norm_num)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball_zero_iff]
    norm_num
  obtain ⟨ε, hε, hεφ⟩ : ∃ ε > 0, ∀ z : ℂ, dist z 0 < ε → z ≠ 0 → g (τ₀ + z • v) ≠ 0 := by
    rcases (hφa 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hgt₁
      have := hφa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected h0 h h1
      simpa [hvdef] using this
    · exact Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
  set ρ : ℝ := min ε 1 / 2 with hρdef
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε 1
    linarith
  have hρ1 : ρ < 3 / 2 := by
    have := min_le_right ε 1
    linarith
  have hsph₀ : ∀ z ∈ sphere (0 : ℂ) ρ, τ₀ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    intro z hz
    have hz' : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    refine ⟨hline τ₀ hτ₀b z (by linarith), hεφ z (by rw [dist_zero_right]; linarith) ?_⟩
    rintro rfl
    rw [norm_zero] at hz'
    linarith
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun z hz => ?_
    have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
    exact hPc.continuousAt.preimage_mem_nhds (hO.mem_nhds (hsph₀ z hz))
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (r / 8) with hδdef
  have hδ : 0 < δ := by positivity
  have hδcl : closedBall τ₀ δ ⊆ ball τ₀ δ₀ := closedBall_subset_ball (by
    have := min_le_left (δ₀ / 2) (r / 8)
    linarith)
  have hδr : ball τ₀ δ ⊆ ball τ₀ (r / 4) := ball_subset_ball (by
    have := min_le_right (δ₀ / 2) (r / 8)
    linarith)
  have hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} :=
    fun τ hτ => hδ₀K (hδcl hτ)
  refine ⟨ball τ₀ δ, ball_mem_nhds τ₀ hδ,
    fun τ => (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • f (τ + z • v)), ?_, ?_⟩
  · have hdiff := differentiableOn_circleAverage hO hf hρ.le hK
    refine DifferentiableOn.congr ((hdiff.const_mul I).const_mul (2 * π * I : ℂ)⁻¹) fun τ _ => ?_
    show (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • f (τ + z • v)) = _
    rw [circleIntegral_inv_smul_eq hρ.ne' (fun z => f (τ + z • v)), smul_eq_mul]
  · intro τ hτ _ hgτ
    have hτr := hδr hτ
    have hh : ∀ z ∈ ball (0 : ℂ) (3 / 2), g (τ + z • v) ≠ 0 →
        DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z := by
      intro z hz hgz
      have h1 : DifferentiableAt ℂ f (τ + z • v) :=
        hf.differentiableAt (hO.mem_nhds ⟨hline τ hτr z (mem_ball_zero_iff.mp hz), hgz⟩)
      exact h1.comp z (hlined τ z)
    have hbd : ∀ z ∈ ball (0 : ℂ) (3 / 2), ∃ N ∈ 𝓝 z, ∃ C, ∀ w ∈ N, w ∈ ball (0 : ℂ) (3 / 2) →
        g (τ + w • v) ≠ 0 → ‖f (τ + w • v)‖ ≤ C := by
      intro z hz
      obtain ⟨N, hN, hNb⟩ := hb _ (hline τ hτr z (mem_ball_zero_iff.mp hz))
      obtain ⟨C, hC⟩ := hNb.exists_norm_le
      exact ⟨(fun w : ℂ => τ + w • v) ⁻¹' N, (hlined τ z).continuousAt.preimage_mem_nhds hN, C,
        fun w hwN hw hgw => hC _ ⟨_, ⟨⟨hwN, hline τ hτr w (mem_ball_zero_iff.mp hw)⟩, hgw⟩, rfl⟩⟩
    have := slice_cauchy (R := 3 / 2) (ψ := fun z => g (τ + z • v)) (h := fun z => f (τ + z • v)) hρ hρ1
      (hgline τ hτr) (fun z hz => (hK τ (ball_subset_closedBall hτ) z hz).2) (by simpa using hgτ) hh hbd
    simpa using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic
