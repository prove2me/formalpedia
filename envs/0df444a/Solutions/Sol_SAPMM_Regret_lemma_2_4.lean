-- Prove2me | solution 1 for SAPMM.Regret.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:25:00.73271+00:00
-- url     : https://prove2.me/submissions/6f836f4b-6ba3-4564-bf81-e0cf607ac2ee

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_2_3

open MeasureTheory ProbabilityTheory

namespace SAPMM.Regret.AuxC

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

end SAPMM.Regret.AuxC

open SAPMM.Regret SAPMM.Regret.AuxC

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n p Ξ) (hP : P.Standing) {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0) (ξ : ℕ → Ω → Ξ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P σ α x0 ξ x lam)
    (hD : 0 < (2 * α - (p : ℝ) * P.κg ^ 2 * σ)) :
    ∀ t ω, ‖x (t + 1) ω - x t ω‖ ≤
      (2 * P.κf + 2 * Real.sqrt p * P.κg * ‖lam t ω‖ + 2 * P.νg * Real.sqrt p * P.κg * σ)
        / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) := by
  intro t ω
  have hxt := x_mem hrun hx0 t ω
  have hxt1 := hrun.x_mem t ω
  have hO := hP.X0_sub_O0 hxt
  have hO1 := hP.X0_sub_O0 hxt1
  have h23 := SAPMM.Regret.lemma_2_3 P hP hσ hα hx0 ξ x lam hrun t ω (x t ω) hxt
  rw [sub_self, norm_zero, norm_sub_rev (x t ω) (x (t + 1) ω)] at h23
  set d := ‖x (t + 1) ω - x t ω‖ with hd
  set c := Real.sqrt p * P.κg with hc
  have hc0 : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) hP.κg_pos.le
  have hc2 : c ^ 2 = (p : ℝ) * P.κg ^ 2 := by
    rw [hc, mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  set L := lam t ω
  set B := L + σ • P.G (x t ω) (ξ t ω) with hB
  set W : EuclideanSpace ℝ (Fin p) :=
    WithLp.toLp 2 (fun i => inner ℝ (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)) with hW
  set A := B + σ • W with hA
  -- subgradient of F
  have hsub := hP.v0_sub (x t ω) hO (ξ t ω) (x (t + 1) ω) hO1
  have hF : P.F (x t ω) (ξ t ω) - P.F (x (t + 1) ω) (ξ t ω) ≤ P.κf * d := by
    have := neg_abs_le (inner ℝ (P.v0 (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω))
    have := abs_real_inner_le_norm (P.v0 (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)
    have := mul_le_mul_of_nonneg_right (hP.v0_bdd (x t ω) hO (ξ t ω)) (norm_nonneg
      (x (t + 1) ω - x t ω))
    simp only at hsub
    linarith
  -- ‖A_+‖ ≤ ‖λ^{t+1}‖
  have hAl : ‖projPos A‖ ≤ ‖lam (t + 1) ω‖ := by
    rw [hrun.lam_succ]
    apply norm_le_of_sum
    apply Finset.sum_le_sum
    intro i _
    simp only [projPos_apply]
    apply pow_le_pow_left₀ (le_max_right _ _)
    apply max_le_max_right
    have hsub := hP.v_sub i (x t ω) hO (ξ t ω) (x (t + 1) ω) hO1
    simp only at hsub
    simp only [hA, hB, hW, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have : σ * (P.G (x t ω) (ξ t ω) i + inner ℝ (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω))
        ≤ σ * P.G (x (t + 1) ω) (ξ t ω) i := mul_le_mul_of_nonneg_left hsub hσ.le
    simp only [L]
    nlinarith
  -- ‖W‖ ≤ c d
  have hWn : ‖W‖ ≤ c * d := by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _)), norm_sq_sum, mul_pow, hc2]
    have : ∀ i ∈ Finset.univ, (W i) ^ 2 ≤ P.κg ^ 2 * d ^ 2 := by
      intro i _
      simp only [hW]
      rw [← sq_abs]
      have h1 := abs_real_inner_le_norm (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)
      have h2 := mul_le_mul_of_nonneg_right (hP.v_bdd i (x t ω) hO (ξ t ω)) (norm_nonneg
        (x (t + 1) ω - x t ω))
      have h3 : |inner ℝ (P.v i (x t ω) (ξ t ω)) (x (t + 1) ω - x t ω)| ≤ P.κg * d := by
        linarith
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    calc ∑ i, (W i) ^ 2 ≤ ∑ _i : Fin p, P.κg ^ 2 * d ^ 2 := Finset.sum_le_sum this
      _ = (p : ℝ) * P.κg ^ 2 * d ^ 2 := by simp; ring
  have hBA : ‖B - A‖ ≤ σ * (c * d) := by
    rw [hA, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left hWn hσ.le
  have hBn : ‖B‖ ≤ ‖L‖ + σ * P.νg := by
    calc ‖B‖ ≤ ‖L‖ + ‖σ • P.G (x t ω) (ξ t ω)‖ := norm_add_le _ _
      _ ≤ ‖L‖ + σ * P.νg := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
        have := hP.G_bdd (x t ω) hO (ξ t ω)
        nlinarith
  have hAn : ‖A‖ ≤ ‖B‖ + ‖B - A‖ := by
    have := norm_sub_norm_le A B
    rw [norm_sub_rev] at this
    linarith
  -- ‖B_+‖² - ‖A_+‖² ≤ (‖B‖ + ‖A‖) ‖B - A‖
  have hdiff : ‖projPos B‖ ^ 2 - ‖projPos A‖ ^ 2 ≤ (‖B‖ + ‖A‖) * ‖B - A‖ := by
    have h1 := norm_projPos_le B
    have h2 := norm_projPos_le A
    have h3 : ‖projPos B‖ - ‖projPos A‖ ≤ ‖B - A‖ :=
      le_trans (norm_sub_norm_le _ _) (projPos_lip B A)
    have h4 := norm_nonneg (projPos A)
    have h5 := norm_nonneg (projPos B)
    rcases le_total ‖projPos A‖ ‖projPos B‖ with h | h
    · have e : ‖projPos B‖ ^ 2 - ‖projPos A‖ ^ 2 =
          (‖projPos B‖ + ‖projPos A‖) * (‖projPos B‖ - ‖projPos A‖) := by ring
      rw [e]
      apply mul_le_mul (by linarith) h3 (by linarith) (by positivity)
    · nlinarith [norm_nonneg (B - A), norm_nonneg B, norm_nonneg A]
  -- combine
  have hl1 : ‖projPos A‖ ^ 2 ≤ ‖lam (t + 1) ω‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hAl 2
  have hmain : α * d ^ 2 ≤ P.κf * d + 1 / (2 * σ) * ((‖B‖ + ‖A‖) * ‖B - A‖) := by
    have : α * d ^ 2 ≤ P.F (x t ω) (ξ t ω) - P.F (x (t + 1) ω) (ξ t ω)
        + 1 / (2 * σ) * (‖projPos B‖ ^ 2 - ‖lam (t + 1) ω‖ ^ 2) := by
      simp only [hB]; nlinarith
    have hs : 0 < 1 / (2 * σ) := by positivity
    have := mul_le_mul_of_nonneg_left (show ‖projPos B‖ ^ 2 - ‖lam (t + 1) ω‖ ^ 2 ≤
      (‖B‖ + ‖A‖) * ‖B - A‖ by linarith) hs.le
    linarith
  have hprod : (‖B‖ + ‖A‖) * ‖B - A‖ ≤ (2 * (‖L‖ + σ * P.νg) + σ * (c * d)) * (σ * (c * d)) := by
    have : 0 ≤ ‖L‖ := norm_nonneg _
    have : 0 ≤ σ * (c * d) := mul_nonneg hσ.le (mul_nonneg hc0 (norm_nonneg _))
    have : 0 ≤ σ * P.νg := mul_nonneg hσ.le hP.νg_pos.le
    apply mul_le_mul _ hBA (norm_nonneg _) (by linarith)
    linarith
  have hmain2 : α * d ^ 2 ≤ P.κf * d + (‖L‖ + σ * P.νg) * (c * d) + σ * c ^ 2 * d ^ 2 / 2 := by
    have hs : 0 < 1 / (2 * σ) := by positivity
    have := mul_le_mul_of_nonneg_left hprod hs.le
    have e : 1 / (2 * σ) * ((2 * (‖L‖ + σ * P.νg) + σ * (c * d)) * (σ * (c * d))) =
        (‖L‖ + σ * P.νg) * (c * d) + σ * c ^ 2 * d ^ 2 / 2 := by
      field_simp
    linarith
  clear_value A W B L c d
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg _
  have hsp := Real.sqrt_nonneg (p : ℝ)
  have hnum : 0 ≤ 2 * P.κf + 2 * Real.sqrt p * P.κg * ‖L‖ + 2 * P.νg * Real.sqrt p * P.κg * σ := by
    have h1 : 0 ≤ Real.sqrt p * P.κg := mul_nonneg hsp hP.κg_pos.le
    have h2 : 0 ≤ Real.sqrt p * P.κg * ‖L‖ := mul_nonneg h1 hL0
    have h3 : 0 ≤ P.νg * (Real.sqrt p * P.κg) * σ := mul_nonneg (mul_nonneg hP.νg_pos.le h1) hσ.le
    have h4 := hP.κf_pos.le
    nlinarith
  rw [le_div_iff₀ hD]
  rcases eq_or_lt_of_le (norm_nonneg (x (t + 1) ω - x t ω)) with h0 | hpos
  · rw [← hd] at h0
    rw [← h0, zero_mul]
    exact hnum
  · rw [← hd] at hpos
    have key : α * d ≤ P.κf + (‖L‖ + σ * P.νg) * c + σ * c ^ 2 * d / 2 := by
      have e1 : α * d ^ 2 = (α * d) * d := by ring
      have e2 : P.κf * d + (‖L‖ + σ * P.νg) * (c * d) + σ * c ^ 2 * d ^ 2 / 2 =
          (P.κf + (‖L‖ + σ * P.νg) * c + σ * c ^ 2 * d / 2) * d := by ring
      rw [e1, e2] at hmain2
      exact le_of_mul_le_mul_right hmain2 hpos
    have e3 : d * (2 * α - (p : ℝ) * P.κg ^ 2 * σ) = 2 * (α * d) - σ * c ^ 2 * d := by
      rw [hc2]; ring
    have e5 : 2 * Real.sqrt p * P.κg * ‖L‖ = 2 * c * ‖L‖ := by rw [hc]; ring
    have e6 : 2 * P.νg * Real.sqrt p * P.κg * σ = 2 * P.νg * c * σ := by rw [hc]; ring
    rw [e3, e5, e6]
    linarith [key]

