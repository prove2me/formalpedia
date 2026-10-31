-- Prove2me | solution 1 for SAPMM.Regret.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:28:51.478883+00:00
-- url     : https://prove2.me/submissions/0d0b84e5-2ad7-4f8e-855e-b93529ab82be

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_lemma_2_2
import Theorems.Thm_SAPMM_Regret_lemma_2_4

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
    ∀ (T : ℕ) (i : Fin p) ω,
      ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ≤
        1 / σ * lam T ω i + 2 * P.κg * P.κf / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * T
          + 2 * Real.sqrt p * P.κg ^ 2 / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * ∑ t ∈ Finset.range T, ‖lam t ω‖
          + 2 * Real.sqrt p * P.νg * P.κg ^ 2 * σ / (2 * α - (p : ℝ) * P.κg ^ 2 * σ) * T := by
  intro T i ω
  have h22 := SAPMM.Regret.lemma_2_2 P hP hσ hα hx0 ξ x lam hrun T i ω
  set D := 2 * α - (p : ℝ) * P.κg ^ 2 * σ
  have hterm : ∀ t ∈ Finset.range T, ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖ ≤
      2 * P.κg * P.κf / D + 2 * Real.sqrt p * P.κg ^ 2 / D * ‖lam t ω‖
        + 2 * Real.sqrt p * P.νg * P.κg ^ 2 * σ / D := by
    intro t _
    have h24 := SAPMM.Regret.lemma_2_4 P hP hσ hα hx0 ξ x lam hrun hD t ω
    have hv := hP.v_bdd i (x t ω) (hP.X0_sub_O0 (x_mem hrun hx0 t ω)) (ξ t ω)
    calc ‖P.v i (x t ω) (ξ t ω)‖ * ‖x (t + 1) ω - x t ω‖
        ≤ P.κg * ((2 * P.κf + 2 * Real.sqrt p * P.κg * ‖lam t ω‖
            + 2 * P.νg * Real.sqrt p * P.κg * σ) / D) :=
          mul_le_mul hv h24 (norm_nonneg _) hP.κg_pos.le
      _ = _ := by field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith
