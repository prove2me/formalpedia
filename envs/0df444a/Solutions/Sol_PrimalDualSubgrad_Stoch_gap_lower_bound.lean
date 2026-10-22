-- Prove2me | solution 1 for PrimalDualSubgrad.Stoch.gap_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:57:54.889935+00:00
-- url     : https://prove2.me/submissions/a0881a57-a869-4a11-b3bb-9238f3282b00

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

set_option autoImplicit false
open Finset MeasureTheory PrimalDualSubgrad.Stoch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

theorem X_betaHat_pos : ∀ n : ℕ, 0 < betaHat n
  | 0 => by simp [betaHat]
  | 1 => by simp [betaHat]
  | (n + 2) => by
    have h := X_betaHat_pos (n + 1)
    rw [betaHat]
    positivity

theorem X_ssaRun_mem (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (f' : E → Ξ → StrongDual ℝ E) (γ : ℝ) (hγ : 0 < γ) (ω : ℕ → Ξ) (i : ℕ) :
    ssaRun π γ x0 f' ω i ∈ Q := by
  cases i with
  | zero => exact hd.x0_mem
  | succ k =>
    show (ssaState π γ x0 f' ω (k + 1)).1 ∈ Q
    simp only [ssaState]
    exact (hπ _ (mul_pos hγ (X_betaHat_pos _)) _).1

theorem X_levelSet_bdd (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (D : ℝ) : ∀ y ∈ levelSet Q d D, ‖y - x0‖ ≤ 4 * D / σ + 1 := by
  intro y ⟨hyQ, hyD⟩
  have hσ := hd.sigma_pos
  have hsc := hd.strongConvexOn
  have hmid : ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • y) ∈ Q :=
    hd.convex hd.x0_mem hyQ (by norm_num) (by norm_num) (by norm_num)
  have h1 := hsc.2 hd.x0_mem hyQ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h2 := hd.x0_isMin _ hmid
  rw [hd.d_x0] at h2 h1
  have h3 : σ / 4 * ‖x0 - y‖ ^ 2 ≤ d y := by
    simp only [smul_eq_mul] at h1
    nlinarith
  have h4 : ‖x0 - y‖ ^ 2 ≤ 4 * D / σ := by
    rw [le_div_iff₀ hσ]
    nlinarith
  rw [norm_sub_rev]
  nlinarith [sq_nonneg (‖x0 - y‖ - 1), norm_nonneg (x0 - y)]

theorem solution (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, expectedCost μ f xstar ≤ expectedCost μ f x)
    (γ : ℝ) (hγ : 0 < γ) (ω : ℕ → Ξ) (k : ℕ) (D : ℝ) (hD : d xstar ≤ D) :
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar)
        ≤ 1 / ((k : ℝ) + 1) * gap Q d (fun i => f' (ssaRun π γ x0 f' ω i) (ω i)) (ssaRun π γ x0 f' ω) k D ∧
      1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), (f (ssaRun π γ x0 f' ω i) (ω i) - f xstar (ω i))
        ≤ 1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar) := by
  have hpos : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  refine ⟨mul_le_mul_of_nonneg_left ?_ hpos, mul_le_mul_of_nonneg_left ?_ hpos⟩
  · -- the sum at x* is bounded by the supremum
    unfold gap
    apply le_csSup
    · refine ⟨∑ i ∈ range (k + 1), ‖f' (ssaRun π γ x0 f' ω i) (ω i)‖ *
        (‖ssaRun π γ x0 f' ω i - x0‖ + (4 * D / σ + 1)), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      apply Finset.sum_le_sum
      intro i _
      have hy' := X_levelSet_bdd Q d σ x0 hd D y hy
      calc f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - y)
          ≤ ‖f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - y)‖ := le_abs_self _
        _ ≤ ‖f' (ssaRun π γ x0 f' ω i) (ω i)‖ * ‖ssaRun π γ x0 f' ω i - y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖f' (ssaRun π γ x0 f' ω i) (ω i)‖ * (‖ssaRun π γ x0 f' ω i - x0‖ + (4 * D / σ + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖ssaRun π γ x0 f' ω i - y‖
                = ‖(ssaRun π γ x0 f' ω i - x0) - (y - x0)‖ := by congr 1; abel
              _ ≤ ‖ssaRun π γ x0 f' ω i - x0‖ + ‖y - x0‖ := norm_sub_le _ _
              _ ≤ _ := by linarith
    · exact ⟨xstar, ⟨hxstar, hD⟩, rfl⟩
  · apply Finset.sum_le_sum
    intro i _
    have hxi := X_ssaRun_mem Q d σ x0 hd π hπ f' γ hγ ω i
    have := hf.subgrad _ hxi (ω i) xstar hxstar
    have h2 : f' (ssaRun π γ x0 f' ω i) (ω i) (xstar - ssaRun π γ x0 f' ω i) =
        -(f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar)) := by
      rw [← map_neg]; congr 1; abel
    linarith
