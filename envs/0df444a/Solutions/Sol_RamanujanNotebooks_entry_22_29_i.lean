-- Prove2me | solution 1 for RamanujanNotebooks.entry_22_29_i
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:36:22.530467+00:00
-- url     : https://prove2.me/submissions/eaf8e18e-7de7-4fef-866e-f483d77aedf2

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_realCbrt

namespace RNE22
open RamanujanNotebooks Real

lemma cbrt_cube (x : ℝ) : realCbrt x ^ 3 = x := by
  unfold realCbrt
  split_ifs with h
  · rw [one_div]; exact Real.rpow_inv_natCast_pow h (by norm_num)
  · have h3 : ((-x) ^ ((3 : ℝ)⁻¹)) ^ 3 = -x := by
      exact_mod_cast Real.rpow_inv_natCast_pow (x := -x) (n := 3) (by linarith) (by norm_num)
    rw [one_div, neg_pow, h3]; ring

lemma cube_inj {y z : ℝ} (h : y ^ 3 = z ^ 3) : y = z :=
  (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h

lemma cbrt_eq {x y : ℝ} (h : y ^ 3 = x) : realCbrt x = y :=
  cube_inj (by rw [cbrt_cube, h])

lemma cos_pi_div_three' : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three

theorem main :
    realCbrt (Real.cos (2 * Real.pi / 9)) + realCbrt (Real.cos (4 * Real.pi / 9)) -
        realCbrt (Real.cos (Real.pi / 9)) =
      realCbrt (3 / 2 * (realCbrt 9 - 2)) := by
  set a := cos (2 * π / 9) with ha_def
  set b := cos (4 * π / 9) with hb_def
  set C := cos (π / 9) with hC_def
  set c := -C with hc_def
  have ha : 8 * a ^ 3 - 6 * a + 1 = 0 := by
    have h := Real.cos_three_mul (2 * π / 9)
    rw [show 3 * (2 * π / 9) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three] at h
    linarith
  have hb : 8 * b ^ 3 - 6 * b + 1 = 0 := by
    have h := Real.cos_three_mul (4 * π / 9)
    rw [show 3 * (4 * π / 9) = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three] at h
    linarith
  have hc : 8 * c ^ 3 - 6 * c + 1 = 0 := by
    have h := Real.cos_three_mul (π / 9)
    rw [show 3 * (π / 9) = π / 3 by ring, Real.cos_pi_div_three] at h
    rw [hc_def]; linarith
  have hpi := Real.pi_pos
  have hab : b < a := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have hb0 : 0 < b := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hC0 : 0 < C := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc0 : c < 0 := by rw [hc_def]; linarith
  have q1 : a ^ 2 + a * b + b ^ 2 = 3 / 4 := by
    have : (a - b) * (8 * (a ^ 2 + a * b + b ^ 2) - 6) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · linarith
  have q2 : a ^ 2 + a * c + c ^ 2 = 3 / 4 := by
    have : (a - c) * (8 * (a ^ 2 + a * c + c ^ 2) - 6) = 0 := by linear_combination ha - hc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · linarith
  have e1 : a + b + c = 0 := by
    have : (b - c) * (a + b + c) = 0 := by linear_combination q1 - q2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by linarith)
    · exact h
  have e2 : a * b + b * c + c * a = -3 / 4 := by
    have : c = -a - b := by linarith
    rw [this]; linear_combination -q1
  have e3 : a * b * c = -1 / 8 := by
    have h3 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by
      have : c = -a - b := by linarith
      rw [this]; ring
    linarith
  -- cube roots
  set u1 := realCbrt a
  set u2 := realCbrt b
  set u3 := realCbrt c
  have hu1 : u1 ^ 3 = a := cbrt_cube a
  have hu2 : u2 ^ 3 = b := cbrt_cube b
  have hu3 : u3 ^ 3 = c := cbrt_cube c
  have hodd : realCbrt C = -u3 := by
    apply cbrt_eq; rw [neg_pow, hu3, hc_def]; ring
  rw [hodd, sub_neg_eq_add]
  set S := u1 + u2 + u3
  set T := u1 * u2 + u2 * u3 + u3 * u1
  set P := u1 * u2 * u3
  have hP : P = -1 / 2 := by
    apply cube_inj
    have : P ^ 3 = u1 ^ 3 * u2 ^ 3 * u3 ^ 3 := by ring
    rw [this, hu1, hu2, hu3, e3]; norm_num
  have E1 : S ^ 3 - 3 * S * T + 3 * P = 0 := by
    have : S ^ 3 - 3 * S * T + 3 * P = u1 ^ 3 + u2 ^ 3 + u3 ^ 3 := by ring
    rw [this, hu1, hu2, hu3, e1]
  have E2 : T ^ 3 - 3 * T * S * P + 3 * P ^ 2 = -3 / 4 := by
    have : T ^ 3 - 3 * T * S * P + 3 * P ^ 2 = u1 ^ 3 * u2 ^ 3 + u2 ^ 3 * u3 ^ 3 + u3 ^ 3 * u1 ^ 3 := by ring
    rw [this, hu1, hu2, hu3, ← e2]
  rw [hP] at E1 E2
  have hm : S * T = (S ^ 3 - 3 / 2) / 3 := by linarith
  have hT : T ^ 3 = -3 / 2 - 3 / 2 * (S * T) := by linarith
  have key : (S * T) ^ 3 = S ^ 3 * T ^ 3 := by ring
  rw [hT, hm] at key
  have h243 : (S ^ 3 + 3) ^ 3 = (3 / 2 * realCbrt 9) ^ 3 := by
    rw [mul_pow, cbrt_cube]
    linear_combination 27 * key
  have hX := cube_inj h243
  symm
  apply cbrt_eq
  linarith

end RNE22

open RamanujanNotebooks in
theorem solution :
    realCbrt (Real.cos (2 * Real.pi / 9)) + realCbrt (Real.cos (4 * Real.pi / 9)) -
        realCbrt (Real.cos (Real.pi / 9)) =
      realCbrt (3 / 2 * (realCbrt 9 - 2)) :=
  RNE22.main
