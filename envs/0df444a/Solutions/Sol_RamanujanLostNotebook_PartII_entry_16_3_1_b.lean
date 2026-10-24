-- Prove2me | solution 1 for RamanujanLostNotebook.PartII.entry_16_3_1_b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:03:11.992335+00:00
-- url     : https://prove2.me/submissions/76331e30-f791-4a2d-9675-9fb15f64e42d

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch16_ch16S
import Definitions.Def_RamanujanLostNotebook_PartII_ch16_ch16STerm

open UpperHalfPlane hiding I σ
open Complex EisensteinSeries
open scoped Real ArithmeticFunction.sigma

namespace S16

lemma G2_I : G2 UpperHalfPlane.I = π := by
  have h := G2_S_transform UpperHalfPlane.I
  have hS : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [modular_S_smul]; ext; simp
  rw [hS] at h
  simp only [UpperHalfPlane.coe_I, I_sq] at h
  have hI : I ≠ 0 := I_ne_zero
  field_simp at h
  linear_combination h / 2

lemma sigma_sum : (∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * I * (UpperHalfPlane.I : ℂ)) ^ (n : ℕ))
    = 1 / 24 - 1 / (8 * π) := by
  have h := G2_eq_tsum_cexp UpperHalfPlane.I
  rw [G2_I, riemannZeta_two] at h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply mul_left_cancel₀ (show (8 * (π : ℂ) ^ 2) ≠ 0 from mul_ne_zero (by norm_num) (pow_ne_zero _ hpi))
  have e : 8 * (π : ℂ) ^ 2 * (1 / (8 * π)) = π := by field_simp
  linear_combination h + e


lemma real_sigma_sum : (∑' n : ℕ+, (σ 1 n : ℝ) * Real.exp (-2 * π) ^ (n : ℕ)) = 1 / 24 - 1 / (8 * π) := by
  have h := sigma_sum
  have hq : cexp (2 * π * I * (UpperHalfPlane.I : ℂ)) = ((Real.exp (-2 * π) : ℝ) : ℂ) := by
    rw [ofReal_exp]; congr 1; simp only [UpperHalfPlane.coe_I]; push_cast; ring_nf; simp
  rw [hq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  push_cast at h ⊢
  exact h

lemma term_eq (n : ℕ) : RamanujanLostNotebook.PartII.ch16STerm 0 n
    = ((n + 1 : ℕ) : ℝ) ^ 1 * Real.exp (-2 * π) ^ (n + 1) / (1 - Real.exp (-2 * π) ^ (n + 1)) := by
  unfold RamanujanLostNotebook.PartII.ch16STerm
  rw [sub_zero, Real.rpow_eq_pow, Real.rpow_one, ← Real.exp_nat_mul]
  simp only [pow_one]
  have h1 : Real.exp (2 * ((n + 1 : ℕ) : ℝ) * π) * Real.exp (((n + 1 : ℕ) : ℝ) * (-2 * π)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hpos : 0 < Real.exp (((n + 1 : ℕ) : ℝ) * (-2 * π)) := Real.exp_pos _
  have hlt : Real.exp (((n + 1 : ℕ) : ℝ) * (-2 * π)) < 1 := by
    rw [Real.exp_lt_one_iff]; push_cast; nlinarith [Real.pi_pos]
  have hne : 1 - Real.exp (((n + 1 : ℕ) : ℝ) * (-2 * π)) ≠ 0 := by linarith
  have hne2 : Real.exp (2 * ((n + 1 : ℕ) : ℝ) * π) - 1 ≠ 0 := by
    intro h0
    have : Real.exp (2 * ((n + 1 : ℕ) : ℝ) * π) = 1 := by linarith
    rw [this, one_mul] at h1; linarith
  rw [div_eq_div_iff hne2 hne]
  linear_combination (-((n + 1 : ℕ) : ℝ)) * h1

lemma hr : ‖Real.exp (-2 * π)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]

lemma summable_term : Summable (RamanujanLostNotebook.PartII.ch16STerm 0) := by
  have h := (summable_pnat_iff_summable_succ (f := fun n : ℕ =>
      (n : ℝ) ^ 1 * Real.exp (-2 * π) ^ n / (1 - Real.exp (-2 * π) ^ n))).1 ?_
  · refine h.congr (fun n => ?_)
    rw [term_eq]
  · -- summability over ℕ+
    have hs : Summable (fun n : ℕ => (n : ℝ) ^ 1 * Real.exp (-2 * π) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
    have hr0 : 0 < Real.exp (-2 * π) := Real.exp_pos _
    have hr1 : Real.exp (-2 * π) < 1 := by
      have := hr; rwa [Real.norm_eq_abs, abs_of_pos hr0] at this
    refine (hs.mul_left (1 / (1 - Real.exp (-2 * π)))).comp_injective PNat.coe_injective |>.of_nonneg_of_le
      (fun n => ?_) (fun n => ?_)
    · have : Real.exp (-2 * π) ^ (n : ℕ) < 1 := pow_lt_one₀ hr0.le hr1 n.ne_zero
      positivity
    · simp only [Function.comp]
      have hp : Real.exp (-2 * π) ^ (n : ℕ) ≤ Real.exp (-2 * π) := by
        exact pow_le_of_le_one hr0.le hr1.le n.ne_zero
      have hd : 0 < 1 - Real.exp (-2 * π) := by linarith
      have hd' : 1 - Real.exp (-2 * π) ≤ 1 - Real.exp (-2 * π) ^ (n : ℕ) := by linarith
      have hnum : 0 ≤ ((n : ℕ) : ℝ) ^ 1 * Real.exp (-2 * π) ^ (n : ℕ) := by positivity
      rw [div_eq_mul_one_div, mul_comm (1 / (1 - Real.exp (-2 * π)))]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hd hd') hnum

lemma tsum_term : (∑' n : ℕ, RamanujanLostNotebook.PartII.ch16STerm 0 n) = 1 / 24 - 1 / (8 * π) := by
  rw [← real_sigma_sum, ← tsum_pow_div_one_sub_eq_tsum_sigma hr 1,
    tsum_pnat_eq_tsum_succ (f := fun m : ℕ =>
      (m : ℝ) ^ 1 * Real.exp (-2 * π) ^ m / (1 - Real.exp (-2 * π) ^ m))]
  refine tsum_congr (fun n => ?_)
  rw [term_eq]

end S16

open RamanujanLostNotebook.PartII in
theorem solution :
    Summable (ch16STerm 0) ∧ ch16S 0 = 1 / (4 * Real.pi) := by
  refine ⟨S16.summable_term, ?_⟩
  unfold ch16S
  rw [S16.tsum_term]
  have h1 : riemannZeta (((0 : ℝ) - 1 : ℝ) : ℂ) = -1 / 12 := by
    have := riemannZeta_neg_nat_eq_bernoulli 1
    push_cast at this ⊢
    rw [show (0 : ℂ) - 1 = -1 by ring, this, bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
    rw [bernoulli'_two]; norm_num
  have h0 : riemannZeta (((0 : ℝ)) : ℂ) = -1 / 2 := by
    push_cast; exact riemannZeta_zero
  have h2 : riemannZeta (((0 : ℝ) - 2 : ℝ) : ℂ) = 0 := by
    have := riemannZeta_neg_two_mul_nat_add_one 0
    push_cast at this ⊢
    rw [show (0 : ℂ) - 2 = -2 * (0 + 1) by ring]; simpa using this
  rw [h1, h0, h2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Complex.div_re, Complex.neg_re, Complex.one_re, Complex.zero_re]
  norm_num
  field_simp
  ring
