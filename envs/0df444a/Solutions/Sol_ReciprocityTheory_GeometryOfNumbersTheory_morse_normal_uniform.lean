-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:59:36.838875+00:00
-- url     : https://prove2.me/submissions/e4ce33ec-48ef-4a44-afb9-e90e56155e76

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseNormSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morse_normal_bound
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {ρ₀ C Λ : ℝ} (hρ₀ : 0 < ρ₀) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (lam : Fin D → ℝ) (φ ν : (Fin D → ℂ) → ℝ)
      (f : (Fin D → ℂ) → ℂ), (∀ j, 0 ≤ lam j ∧ lam j ≤ Λ) →
      ContinuousOn φ (Metric.ball 0 ρ₀) → ContinuousOn ν (Metric.ball 0 ρ₀) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  set R := min (ρ₀ / 2) (1 / (2 * (C + 1))) with hRdef
  have hC1 : 0 < C + 1 := by linarith
  have hR : 0 < R := lt_min (by linarith) (by positivity)
  have hRρ : R < ρ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hCR : C * R ≤ 1 / 2 := by
    have h1 : R ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    have h2 : (C + 1) * R ≤ 1 / 2 := by
      calc (C + 1) * R ≤ (C + 1) * (1 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC1.le
        _ = 1 / 2 := by field_simp
    nlinarith
  set G := discI Λ R ^ D with hG
  have hG0 : 0 < G := pow_pos (discI_pos hΛ hR) D
  set E := Real.exp (-(C * R ^ 3)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨2 / (G * E), by positivity, ?_⟩
  intro n hnpos lam φ ν f hlam hφc hνc hφ hν hν0 hf hint
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hnpos)
  have hRs : R / Real.sqrt n ≤ R := div_le_self hR.le hs1
  have hφ' : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      φ z ≤ ∑ j, (fun _ => Λ) j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3 := by
    intro z hz
    refine (hφ z hz).trans ?_
    gcongr with j
    exact (hlam j).2
  have hCRs : C * (R / Real.sqrt n) ≤ C * R := mul_le_mul_of_nonneg_left hRs hC
  have B := morse_normal_bound hC (fun _ => Λ) (fun _ => hΛ) φ ν hφc hνc hφ' hν f hf n hnpos R hR
    (hRs.trans_lt hRρ) (by linarith)
  have hprod : ∏ _j : Fin D, discI Λ R = G := by simp [hG]
  rw [hprod] at B
  set h := Real.exp (-(C * R ^ 3 / Real.sqrt n)) * (1 - C * (R / Real.sqrt n)) with hh
  have hhE : E / 2 ≤ h := by
    have e1 : E ≤ Real.exp (-(C * R ^ 3 / Real.sqrt n)) := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have : C * R ^ 3 / Real.sqrt n ≤ C * R ^ 3 := div_le_self (by positivity) hs1
      linarith
    have e2 : (1 : ℝ) / 2 ≤ 1 - C * (R / Real.sqrt n) := by linarith
    calc E / 2 = E * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul e1 e2 (by norm_num) (Real.exp_pos _).le
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hhE
  have hsub : Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n) ⊆ Metric.ball 0 ρ₀ :=
    Metric.ball_subset_ball (hRs.trans hRρ.le)
  have hI : ∫ z in Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    apply setIntegral_mono_set hint
    · exact ae_restrict_of_forall_mem measurableSet_ball (fun z hz =>
        mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hν0 z hz))
    · exact Eventually.of_forall hsub
  set I := ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball (fun z hz =>
        mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hν0 z hz))
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := pow_pos hn' D
  have hB' : ‖f 0‖ ^ 2 * (G / (n : ℝ) ^ D) * h ≤ I := B.trans hI
  have e : ‖f 0‖ ^ 2 = (‖f 0‖ ^ 2 * (G / (n : ℝ) ^ D) * h) * ((n : ℝ) ^ D * (G⁻¹ / h)) := by
    field_simp
  have key : G⁻¹ / h ≤ 2 / (G * E) := by
    rw [div_le_div_iff₀ hh0 (by positivity)]
    have : G⁻¹ * (G * E) = E := by field_simp
    nlinarith
  calc ‖f 0‖ ^ 2 = _ := e
    _ ≤ I * ((n : ℝ) ^ D * (G⁻¹ / h)) :=
        mul_le_mul_of_nonneg_right hB' (by positivity)
    _ ≤ I * ((n : ℝ) ^ D * (2 / (G * E))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hnD.le) hI0
    _ = _ := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
