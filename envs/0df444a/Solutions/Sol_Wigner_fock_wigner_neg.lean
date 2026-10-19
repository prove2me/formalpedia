-- Prove2me | solution 1 for Wigner.fock_wigner_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:50:10.689641+00:00
-- url     : https://prove2.me/submissions/53ebeacb-f9e3-4a29-a248-a01a9564b127

import Mathlib
import Definitions.Def_wigner
import Definitions.Def_wigner_states

open MeasureTheory
open Wigner

theorem solution : wigner (fockState 1) 1 0 0 < 0 := by
  let r : ℝ → ℝ := fun y => Real.pi ^ (-(1 / 4 : ℝ)) * (2 * y) * Real.exp (-(y ^ 2) / 2) /
      Real.sqrt ((2 : ℝ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℝ))
  have hψ : ∀ y, fockState 1 y = ((r y : ℝ) : ℂ) := by
    intro y; simp only [fockState, hermiteP, r]
  have hr_neg : ∀ y, r (-y) = - r y := by
    intro y; simp only [r, neg_sq]; ring
  have hint_eq : ∀ y, wignerIntegrand (fockState 1) 1 0 0 y = ((-(r y ^ 2) : ℝ) : ℂ) := by
    intro y
    simp only [wignerIntegrand, hψ, zero_add, zero_sub, hr_neg, Complex.conj_ofReal, mul_zero, zero_mul,
      zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    push_cast; ring
  have hK : 0 < Real.sqrt ((2 : ℝ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℝ)) := by
    apply Real.sqrt_pos.2; norm_num
  have hsq : ∀ y, r y ^ 2 = (Real.pi ^ (-(1 / 4 : ℝ)) * 2 /
      Real.sqrt ((2 : ℝ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℝ))) ^ 2 * (y ^ (2 : ℝ) * Real.exp (-1 * y ^ 2)) := by
    intro y
    have he : Real.exp (-(y ^ 2) / 2) ^ 2 = Real.exp (-1 * y ^ 2) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [Real.rpow_two]
    simp only [r]
    rw [div_pow, mul_pow, mul_pow, he, div_pow, mul_pow]
    ring
  have hint : Integrable (fun y => r y ^ 2) volume := by
    have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)).const_mul
      ((Real.pi ^ (-(1 / 4 : ℝ)) * 2 / Real.sqrt ((2 : ℝ) ^ 1 * ((Nat.factorial 1 : ℕ) : ℝ))) ^ 2)
    refine this.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [hsq, neg_mul, one_mul]
  have hpos : 0 < ∫ y, r y ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg _) hint]
    have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun y => r y ^ 2) := by
      intro y hy
      simp only [Function.mem_support]
      have : 0 < r y := by
        simp only [r]
        have hy' : (0 : ℝ) < y := hy
        positivity
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp
  have hW : wignerIntegral (fockState 1) 1 0 0 = ((-(∫ y, r y ^ 2) : ℝ) : ℂ) := by
    unfold wignerIntegral
    simp only [hint_eq]
    rw [← integral_neg, integral_complex_ofReal]
  unfold wigner
  rw [hW, Complex.ofReal_re]
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

