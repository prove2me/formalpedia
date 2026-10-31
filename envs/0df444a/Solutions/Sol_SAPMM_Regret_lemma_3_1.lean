-- Prove2me | solution 1 for SAPMM.Regret.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:24:59.535828+00:00
-- url     : https://prove2.me/submissions/4e309678-f573-4d25-a563-d23fd7c706b1

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_2_3

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
    ∀ (T : ℕ) ω, ∀ y ∈ P.X0,
      ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ≤
        ∑ t ∈ Finset.range T, P.F y (ξ t ω) + P.κf ^ 2 / (2 * α) * T + α / 2 * P.D0 ^ 2
          + σ / 2 * P.νg ^ 2 * T
          + ∑ t ∈ Finset.range T, inner ℝ (lam t ω) (P.G y (ξ t ω)) := by
  intro T ω y hy
  have h23 := SAPMM.Regret.lemma_2_3 P hP hσ hα hx0 ξ x lam hrun
  -- one-step inequality
  have step : ∀ t, P.F (x t ω) (ξ t ω) ≤ P.F y (ξ t ω) + P.κf ^ 2 / (2 * α)
      + (1 / (2 * σ) * ‖lam t ω‖ ^ 2 - 1 / (2 * σ) * ‖lam (t + 1) ω‖ ^ 2)
      + inner ℝ (lam t ω) (P.G y (ξ t ω)) + σ / 2 * P.νg ^ 2
      + (α / 2 * ‖y - x t ω‖ ^ 2 - α / 2 * ‖y - x (t + 1) ω‖ ^ 2) := by
    intro t
    have h1 := h23 t ω y hy
    have hxt := x_mem hrun hx0 t ω
    have hxt1 := hrun.x_mem t ω
    -- projection bound
    have hG : ‖P.G y (ξ t ω)‖ ≤ P.νg := hP.G_bdd _ (hP.X0_sub_O0 hy) _
    have hsG : ‖σ • P.G y (ξ t ω)‖ = σ * ‖P.G y (ξ t ω)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    have h2 : ‖projPos (lam t ω + σ • P.G y (ξ t ω))‖ ^ 2 ≤
        ‖lam t ω + σ • P.G y (ξ t ω)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_projPos_le _) 2
    rw [norm_add_sq_real, hsG, real_inner_smul_right] at h2
    have h3 : ‖P.G y (ξ t ω)‖ ^ 2 ≤ P.νg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
    have h2' : ‖projPos (lam t ω + σ • P.G y (ξ t ω))‖ ^ 2 ≤ ‖lam t ω‖ ^ 2
        + 2 * σ * inner ℝ (lam t ω) (P.G y (ξ t ω)) + σ ^ 2 * P.νg ^ 2 := by
      nlinarith [sq_nonneg σ]
    have h2'' : 1 / (2 * σ) * ‖projPos (lam t ω + σ • P.G y (ξ t ω))‖ ^ 2 ≤
        1 / (2 * σ) * ‖lam t ω‖ ^ 2 + inner ℝ (lam t ω) (P.G y (ξ t ω)) + σ / 2 * P.νg ^ 2 := by
      have hc : 0 < 1 / (2 * σ) := by positivity
      have := mul_le_mul_of_nonneg_left h2' hc.le
      have e : 1 / (2 * σ) * (‖lam t ω‖ ^ 2 + 2 * σ * inner ℝ (lam t ω) (P.G y (ξ t ω))
          + σ ^ 2 * P.νg ^ 2) = 1 / (2 * σ) * ‖lam t ω‖ ^ 2 + inner ℝ (lam t ω) (P.G y (ξ t ω))
          + σ / 2 * P.νg ^ 2 := by field_simp
      linarith
    -- subgradient bound
    have hsub := hP.v0_sub (x t ω) (hP.X0_sub_O0 hxt) (ξ t ω) (x (t + 1) ω) (hP.X0_sub_O0 hxt1)
    have hcs : inner ℝ (P.v0 (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω) ≥
        -(P.κf * ‖x (t + 1) ω - x t ω‖) := by
      have := abs_real_inner_le_norm (P.v0 (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)
      have hb := hP.v0_bdd (x t ω) (hP.X0_sub_O0 hxt) (ξ t ω)
      have := mul_le_mul_of_nonneg_right hb (norm_nonneg (x (t + 1) ω - x t ω))
      have := neg_abs_le (inner ℝ (P.v0 (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω))
      linarith
    have hq := kf_quad P.κf α ‖x (t + 1) ω - x t ω‖ hα
    linarith
  -- telescoping by induction
  have hind : ∀ T, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ≤
      ∑ t ∈ Finset.range T, P.F y (ξ t ω) + P.κf ^ 2 / (2 * α) * T
        + (1 / (2 * σ) * ‖lam 0 ω‖ ^ 2 - 1 / (2 * σ) * ‖lam T ω‖ ^ 2)
        + ∑ t ∈ Finset.range T, inner ℝ (lam t ω) (P.G y (ξ t ω)) + σ / 2 * P.νg ^ 2 * T
        + (α / 2 * ‖y - x 0 ω‖ ^ 2 - α / 2 * ‖y - x T ω‖ ^ 2) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have := step T
      push_cast
      linarith
  have h0 := hind T
  rw [hrun.lam_zero, hrun.x_zero, norm_zero] at h0
  have hD : ‖y - x0‖ ^ 2 ≤ P.D0 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hP.diam y hy x0 hx0) 2
  have : 0 ≤ 1 / (2 * σ) * ‖lam T ω‖ ^ 2 := by positivity
  have : 0 ≤ α / 2 * ‖y - x T ω‖ ^ 2 := by positivity
  have : α / 2 * ‖y - x0‖ ^ 2 ≤ α / 2 * P.D0 ^ 2 := mul_le_mul_of_nonneg_left hD (by positivity)
  nlinarith

