-- Prove2me | solution 1 for SZ.fract_eq_zero_of_even_floors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:26.376806+00:00
-- url     : https://prove2.me/submissions/191ff321-a50f-4b53-8ed1-52a7c2ee13dd

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
import Theorems.Thm_SZ_fract_lt_half
import Theorems.Thm_SZ_fract_two_mul

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    Int.fract t = 0 := by
  have hhalf : ∀ k : ℕ, Int.fract (t * 2 ^ k) < 1 / 2 := by
    intro k
    refine fract_lt_half (h k) ?_
    have e : (2 : ℝ) * (t * 2 ^ k) = t * 2 ^ (k + 1) := by ring
    rw [e]; exact h (k + 1)
  have hpow : ∀ k : ℕ, Int.fract (t * 2 ^ k) = 2 ^ k * Int.fract t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : t * 2 ^ (k + 1) = 2 * (t * 2 ^ k) := by ring
      rw [e, fract_two_mul (hhalf k), ih]
      ring
  by_contra hne
  have hpos : 0 < Int.fract t := lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hne)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2 : ℝ) ^ j < Int.fract t :=
    exists_pow_lt_of_lt_one hpos (by norm_num)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hone : (1 : ℝ) < 2 ^ j * Int.fract t := by
    have e : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [div_pow]; norm_num
    rw [e] at hj
    have := mul_lt_mul_of_pos_left hj h2j
    rwa [mul_one_div, div_self (ne_of_gt h2j)] at this
  have := hhalf j
  rw [hpow j] at this
  linarith
end SZ
