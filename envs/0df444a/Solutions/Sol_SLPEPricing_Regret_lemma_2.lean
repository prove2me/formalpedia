-- Prove2me | solution 1 for SLPEPricing.Regret.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:35:58.314682+00:00
-- url     : https://prove2.me/submissions/fd63c827-0c81-4377-a5e7-cbfa0f7803ff

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open SLPEPricing.Regret

theorem solution (d : ℝ → ℝ) (pstar Ψ Ψbar K₁ : ℝ) (hd : ContDiff ℝ 3 d)
    (hΨ : 0 < Ψ) (hΨbar : 0 < Ψbar)
    (hr2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv 2 (r d) x - iteratedDeriv 2 (r d) y| ≤ Ψ * |x - y|)
    (hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |deriv d x - deriv d y| ≤ Ψbar * |x - y|)
    (hpos : 0 < pstar) (hlt : pstar < 1)
    (hmax : ∀ p ∈ Set.Icc (0 : ℝ) 1, r d p ≤ r d pstar)
    (hd2 : iteratedDeriv 2 d pstar = 0)
    (hK₁ : ∀ k ≤ 3, ∀ p ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv k d p| ≤ K₁) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1,
      pstar * (deriv d p - deriv d pstar) ≤ (Ψ + Ψbar + 2 * K₁) * (p - pstar) ^ 2 := by
  intro p hp
  have h2 : ContDiff ℝ 2 (deriv d) := by
    have h3 : ContDiff ℝ (2 + 1) d := by convert hd using 1; rfl
    rw [contDiff_succ_iff_deriv] at h3
    exact h3.2.2
  have hdd : Differentiable ℝ (deriv d) := h2.differentiable (by norm_num)
  have h1' : ContDiff ℝ 1 (deriv (deriv d)) := by
    have h3 : ContDiff ℝ (1 + 1) (deriv d) := by convert h2 using 1; rfl
    rw [contDiff_succ_iff_deriv] at h3
    exact h3.2.2
  have hddd : Differentiable ℝ (deriv (deriv d)) := h1'.differentiable (by norm_num)
  have hb3 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (deriv d)) x| ≤ K₁ := fun x hx => by
    have := hK₁ 3 le_rfl x hx
    simpa [iteratedDeriv_succ] using this
  have hd2' : deriv (deriv d) pstar = 0 := by simpa [iteratedDeriv_succ] using hd2
  have hK : 0 ≤ K₁ := le_trans (abs_nonneg _) (hK₁ 0 (by norm_num) 0 (by norm_num))
  set S := Set.uIcc pstar p with hS
  have hSsub : S ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx <;> constructor <;>
      linarith [hx.1, hx.2, hp.1, hp.2]
  have hconv : Convex ℝ S := convex_uIcc _ _
  have hpS : pstar ∈ S := Set.left_mem_uIcc
  have hpS' : p ∈ S := Set.right_mem_uIcc
  have hdist : ∀ x ∈ S, |x - pstar| ≤ |p - pstar| := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx
    · rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith [hx.1, hx.2])]
      linarith [hx.2]
    · rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith [hx.1, hx.2])]
      linarith [hx.1]
  have hsec : ∀ x ∈ S, ‖deriv (deriv d) x‖ ≤ K₁ * |p - pstar| := by
    intro x hx
    have := hconv.norm_image_sub_le_of_norm_deriv_le (fun y _ => hddd y)
      (fun y hy => by rw [Real.norm_eq_abs]; exact hb3 y (hSsub hy)) hpS hx
    rw [hd2', sub_zero, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs]
    calc |deriv (deriv d) x| ≤ K₁ * |x - pstar| := this
      _ ≤ K₁ * |p - pstar| := mul_le_mul_of_nonneg_left (hdist x hx) hK
  have := hconv.norm_image_sub_le_of_norm_deriv_le (fun y _ => hdd y) hsec hpS hpS'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hsq : |p - pstar| * |p - pstar| = (p - pstar) ^ 2 := by
    rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
  have hle : deriv d p - deriv d pstar ≤ K₁ * (p - pstar) ^ 2 := by
    have := le_abs_self (deriv d p - deriv d pstar)
    nlinarith
  have hsq0 : 0 ≤ (p - pstar) ^ 2 := sq_nonneg _
  have : pstar * (deriv d p - deriv d pstar) ≤ K₁ * (p - pstar) ^ 2 := by
    rcases le_total 0 (deriv d p - deriv d pstar) with h0 | h0
    · nlinarith
    · nlinarith
  nlinarith
