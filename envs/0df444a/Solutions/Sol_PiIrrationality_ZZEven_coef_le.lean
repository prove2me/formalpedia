-- Prove2me | solution 1 for PiIrrationality.ZZEven.coef_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:47:26.523161+00:00
-- url     : https://prove2.me/submissions/6e6bc470-659e-4db8-aaaf-daa80b61827a

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

namespace PiIrrationality.ZZEven.CoefLe

/-- A single term of the negative binomial series is at most its sum. -/
lemma choose_mul_pow_le (d j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (Nat.choose (j + d) d : ℝ) * x ^ j ≤ ((1 - x)⁻¹) ^ (d + 1) := by
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have h := hasSum_choose_mul_geometric_of_norm_lt_one' (R := ℝ) d hnorm
  have hinv : Ring.inverse (1 - x) = (1 - x)⁻¹ := Ring.inverse_eq_inv _
  rw [hinv] at h
  exact le_hasSum h j fun i _ => by positivity

/-- The real evaluation of `A`. -/
noncomputable def Aval (x : ℝ) : ℝ :=
  (1 + x) ^ 4 * (2 + 6 * x + 9 * x ^ 2 + 6 * x ^ 3 + 2 * x ^ 4) ^ 4

lemma eval₂_A (x : ℝ) : (A.eval₂ (Nat.castRingHom ℝ) x) = Aval x := by
  simp [A, Aval, eval₂_mul, eval₂_pow, eval₂_add, eval₂_X, eval₂_one]

/-- Partial sums of a polynomial with natural coefficients are below its value. -/
lemma partial_le_eval (p : ℕ[X]) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ k ∈ Finset.range m, (p.coeff k : ℝ) * x ^ k ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  rw [eval₂_eq_sum_range' (Nat.castRingHom ℝ) (n := p.natDegree + m + 1) (by omega)]
  simp only [Nat.coe_castRingHom]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k _ _; positivity

theorem coef_le_pow (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (coef n : ℝ) ≤ (Aval x / (x ^ 6 * (1 - x) ^ 8)) ^ n := by
  have h1x : 0 < 1 - x := by linarith
  have h1x' : 1 - x ≠ 0 := h1x.ne'
  have hx' : x ≠ 0 := hx0.ne'
  unfold coef
  push_cast
  have hterm : ∀ k ∈ Finset.range (6 * n + 1),
      ((A ^ n).coeff k : ℝ) * (Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k) : ℝ) ≤
        ((A ^ n).coeff k : ℝ) * x ^ k * (x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n) := by
    intro k hk
    have hk' : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using hk
    have hc := choose_mul_pow_le (8 * n - 1) (6 * n - k) hx0.le hx1
    rw [show 8 * n - 1 + 1 = 8 * n by omega] at hc
    rw [show 8 * n - 1 + (6 * n - k) = (6 * n - k) + (8 * n - 1) by ring,
      Nat.choose_symm_add]
    have hxk : x ^ k * (x ^ (6 * n))⁻¹ = (x ^ (6 * n - k))⁻¹ := by
      rw [show 6 * n = (6 * n - k) + k by omega, pow_add]
      field_simp
      rw [show 6 * n - k + k - k = 6 * n - k by omega]
    have hcoef : (0 : ℝ) ≤ ((A ^ n).coeff k : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc ((A ^ n).coeff k : ℝ), mul_assoc ((A ^ n).coeff k : ℝ)]
    apply mul_le_mul_of_nonneg_left _ hcoef
    rw [hxk]
    have hpos : 0 < x ^ (6 * n - k) := pow_pos hx0 _
    rw [le_inv_mul_iff₀ hpos, mul_comm]
    exact hc
  calc ∑ k ∈ Finset.range (6 * n + 1),
        ((A ^ n).coeff k : ℝ) * (Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k) : ℝ)
      ≤ ∑ k ∈ Finset.range (6 * n + 1),
          ((A ^ n).coeff k : ℝ) * x ^ k * (x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (6 * n + 1), ((A ^ n).coeff k : ℝ) * x ^ k) *
          ((x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n)) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ (A ^ n).eval₂ (Nat.castRingHom ℝ) x * ((x ^ (6 * n))⁻¹ * ((1 - x)⁻¹) ^ (8 * n)) := by
        apply mul_le_mul_of_nonneg_right (partial_le_eval _ _ hx0.le); positivity
    _ = (Aval x / (x ^ 6 * (1 - x) ^ 8)) ^ n := by
        rw [eval₂_pow, eval₂_A, div_pow, mul_pow, ← pow_mul, ← pow_mul]
        field_simp
        rw [one_div_pow, mul_assoc, one_div_mul_cancel (pow_ne_zero _ h1x'), mul_one]

end PiIrrationality.ZZEven.CoefLe

open PiIrrationality.ZZEven PiIrrationality.ZZEven.CoefLe in
theorem solution (n : ℕ) :
    (PiIrrationality.ZZEven.coef n : ℝ) ≤ Real.exp (1722 / 100 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coef]
  have h := coef_le_pow n hn (x := 6 / 25) (by norm_num) (by norm_num)
  refine h.trans ?_
  rw [show (1722 / 100 : ℝ) * n = n * (1722 / 100) by ring, Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by unfold Aval; positivity)
  -- exp (17.22) = exp 1 ^ 17 * exp 0.22
  have he : Real.exp (1722 / 100) = Real.exp 1 ^ 17 * Real.exp (22 / 100) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [he]
  have h1 := Real.exp_one_gt_d9
  have h2 : (1 : ℝ) + 22 / 100 + (22 / 100) ^ 2 / 2 ≤ Real.exp (22 / 100) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h3 : (2.7182818283 : ℝ) ^ 17 ≤ Real.exp 1 ^ 17 :=
    pow_le_pow_left₀ (by norm_num) h1.le 17
  calc Aval (6 / 25) / ((6 / 25) ^ 6 * (1 - 6 / 25) ^ 8)
      ≤ (2.7182818283 : ℝ) ^ 17 * (1 + 22 / 100 + (22 / 100) ^ 2 / 2) := by
        unfold Aval; norm_num
    _ ≤ Real.exp 1 ^ 17 * Real.exp (22 / 100) := by
        apply mul_le_mul h3 h2 (by norm_num) (by positivity)
