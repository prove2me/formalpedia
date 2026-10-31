-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:20:28.808008+00:00
-- url     : https://prove2.me/submissions/5973cc01-9310-4097-9e33-d74962d03fc5

import Mathlib
import Definitions.Def_SAPMM_Regret_Model

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxB

open SAPMM.Regret

lemma projPos_apply {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    projPos y i = max (y i) 0 := rfl

lemma norm_sq_sum {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq y

lemma norm_le_of_sum {p : ℕ} {a b : EuclideanSpace ℝ (Fin p)}
    (h : ∑ i, (a i) ^ 2 ≤ ∑ i, (b i) ^ 2) : ‖a‖ ≤ ‖b‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_sum, norm_sq_sum]
  exact h

lemma norm_projPos_le {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) : ‖projPos y‖ ≤ ‖y‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  rw [projPos_apply]
  rcases le_total (y i) 0 with h | h
  · rw [max_eq_right h]; simpa using sq_nonneg (y i)
  · rw [max_eq_left h]

lemma projPos_lip {p : ℕ} (a b : EuclideanSpace ℝ (Fin p)) :
    ‖projPos a - projPos b‖ ≤ ‖a - b‖ := by
  apply norm_le_of_sum
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, projPos_apply]
  have := abs_max_sub_max_le_abs (a i) (b i) 0
  rw [← sq_abs (max (a i) 0 - max (b i) 0), ← sq_abs (a i - b i)]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma projPos_of_nonneg {p : ℕ} (y : EuclideanSpace ℝ (Fin p)) (h : ∀ i, 0 ≤ y i) :
    projPos y = y := by
  ext i
  rw [projPos_apply, max_eq_left (h i)]

section run

variable {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Problem n p Ξ} {σ α : ℝ} {x0 : EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {x : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {lam : ℕ → Ω → EuclideanSpace ℝ (Fin p)}

lemma lam_nonneg (hrun : IsRun P σ α x0 ξ x lam) : ∀ t ω i, 0 ≤ lam t ω i := by
  intro t ω i
  cases t with
  | zero => rw [hrun.lam_zero]; simp
  | succ t => rw [hrun.lam_succ, projPos_apply]; exact le_max_right _ _

lemma x_mem (hrun : IsRun P σ α x0 ξ x lam) (hx0 : x0 ∈ P.X0) : ∀ t ω, x t ω ∈ P.X0 := by
  intro t ω
  cases t with
  | zero => rw [hrun.x_zero]; exact hx0
  | succ t => exact hrun.x_mem t ω

end run



lemma kf_quad (k a d : ℝ) (ha : 0 < a) : k * d - a / 2 * d ^ 2 ≤ k ^ 2 / (2 * a) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (k - a * d)]

end SAPMM.Regret.AuxB

open SAPMM.Regret SAPMM.Regret.AuxB

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam) :
    ∀ (T : ℕ) (i : Fin p) ω,
      ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ≤
        1 / σ * lam T ω i
          + ∑ t ∈ Finset.range T, ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ := by
  intro T i ω
  have step : ∀ t, P.G (x t ω) (ξ t ω) i ≤ 1 / σ * lam (t + 1) ω i - 1 / σ * lam t ω i
      + ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ := by
    intro t
    have hxt := x_mem hrun hx0 t ω
    have hxt1 := hrun.x_mem t ω
    have hsub := hP.v_sub i (x t ω) (hP.X0_sub_O0 hxt) (ξ t ω) (x (t + 1) ω)
      (hP.X0_sub_O0 hxt1)
    have hcs := neg_abs_le (inner ℝ (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω))
    have hcs2 := abs_real_inner_le_norm (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)
    have hl : lam t ω i + σ * P.G (x (t + 1) ω) (ξ t ω) i ≤ lam (t + 1) ω i := by
      rw [hrun.lam_succ, projPos_apply]
      refine le_trans (le_of_eq ?_) (le_max_left _ _)
      simp
    simp only at hsub
    have key : σ * P.G (x t ω) (ξ t ω) i ≤ lam (t + 1) ω i - lam t ω i
        + σ * (‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖) := by nlinarith
    have e1 : 1 / σ * lam (t + 1) ω i - 1 / σ * lam t ω i
        + ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ = (lam (t + 1) ω i - lam t ω i
        + σ * (‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖)) / σ := by
      field_simp
    rw [e1, le_div_iff₀ hσ]
    linarith
  have hind : ∀ T, ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ≤
      1 / σ * lam T ω i - 1 / σ * lam 0 ω i
        + ∑ t ∈ Finset.range T, ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := step T
      linarith
  have := hind T
  rw [hrun.lam_zero] at this
  simpa using this
