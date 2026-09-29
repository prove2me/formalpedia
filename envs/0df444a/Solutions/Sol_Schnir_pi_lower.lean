-- Prove2me | solution 1 for Schnir.pi_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:10.767987+00:00
-- url     : https://prove2.me/submissions/6a358887-77e8-4b42-9c5e-e06a679dda70

import Mathlib
import Definitions.Def_Schnir_defs

open Finset Real

namespace Schnir

lemma cheb_log_le_lin (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / 1000 - 1 + 10 * Real.log 2 := by
  have h1 : Real.log y = Real.log (y / 1024) + Real.log 1024 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; field_simp
  have h2 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_le_sub_one_of_pos (show 0 < y / 1024 by positivity)
  rw [h1, h2]
  have : y / 1024 ≤ y / 1000 := by
    apply div_le_div_of_nonneg_left hy.le (by norm_num) (by norm_num)
  linarith

/-- Note eq. (3): `π(y) - 1 ≥ 2y / (3 log y)` for `y ≥ 1000`. -/
theorem pi_lower (y : ℝ) (hy : 1000 ≤ y) :
    2 * y / (3 * Real.log y) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) - 1 := by
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have h := Chebyshev.pi_ge' (x := y) (by linarith)
  rw [div_le_iff₀ hlog] at h
  rw [div_le_iff₀ (by positivity)]
  have a1 := cheb_log_le_lin y (by linarith)
  have a2 := cheb_log_le_lin (y + 2) (by linarith)
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  nlinarith

lemma cheb_card_odd_primes (M : ℕ) (hM : 2 ≤ M) :
    ((Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : (Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
      = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

end Schnir

open Schnir in
theorem solution (y : ℝ) (hy : 1000 ≤ y) :
    2 * y / (3 * Real.log y) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) - 1 :=
  Schnir.pi_lower y hy
