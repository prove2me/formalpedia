-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:52:08.665733+00:00
-- url     : https://prove2.me/submissions/8442e434-9ec1-40fb-a960-b245692862b5

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_to_1e8
import Theorems.Thm_TaoFivePrimes_mertens_tail_upper
import Theorems.Thm_TaoFivePrimes_mertens_product_error_absorption_512
import Theorems.Thm_TaoFivePrimes_mertens_reciprocal_endpoint_certificate_511
import Mathlib

open scoped BigOperators

theorem solution (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log x) ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  by_cases h512 : 512 ≤ x
  · let P : ℝ := ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)
    have hp2 (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hfactor (p : ℕ) (hp : p ∈ Nat.primesLE ⌊x⌋₊) :
        0 < (p : ℝ) / ((p : ℝ) - 1) :=
      div_pos (by have := hp2 p hp; linarith) (by have := hp2 p hp; linarith)
    have hP : 0 < P := Finset.prod_pos hfactor
    have hsplit : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
        Real.log P + ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
      rw [show Real.log P = ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          Real.log ((p : ℝ) / ((p : ℝ) - 1)) from
        Real.log_prod (fun p hp => ne_of_gt (hfactor p hp))]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by have := hp2 p hp; linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by have := hp2 p hp; linarith
      have heq : 1 - 1 / (p : ℝ) = ((p : ℝ) / ((p : ℝ) - 1))⁻¹ := by
        field_simp [hp0, hp1]
      rw [heq, Real.log_inv]
      ring
    have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hupper := TaoFivePrimes.rosser_schoenfeld_product_bound_to_1e8 x hxpos hsmall
    have hlogupper := Real.log_lt_log hP hupper
    have heq : Real.exp Real.eulerMascheroniConstant * Real.log x +
          2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x =
        Real.exp Real.eulerMascheroniConstant * Real.log x *
          (1 + 2 / (Real.sqrt x * Real.log x)) := by
      field_simp [ne_of_gt hsqrt, ne_of_gt hlog]
      <;> ring
    have hepos : 0 < 1 + 2 / (Real.sqrt x * Real.log x) := by positivity
    rw [heq, Real.log_mul (by positivity : Real.exp Real.eulerMascheroniConstant * Real.log x ≠ 0)
      (ne_of_gt hepos), Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hlog),
      Real.log_exp] at hlogupper
    have hlogerr := Real.log_le_sub_one_of_pos hepos
    have htail := TaoFivePrimes.mertens_tail_upper x hx
    have herr := TaoFivePrimes.mertens_product_error_absorption_512 x h512
    rw [hsplit]
    linarith
  · have hn : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hxpos.le).2 hx
    have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
    have hxnext : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hn511 : ⌊x⌋₊ ≤ 511 := by
      have : (⌊x⌋₊ : ℝ) < 512 := by linarith
      have : ⌊x⌋₊ < 512 := by exact_mod_cast this
      omega
    have hnreal : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
    have hnlog : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
    have hmain : Real.log (Real.log (⌊x⌋₊ : ℝ)) ≤ Real.log (Real.log x) :=
      Real.log_le_log hnlog (Real.log_le_log (by linarith) hnx)
    have hlognext : Real.log x ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) :=
      Real.log_le_log hxpos hxnext.le
    have hpow : (Real.log x) ^ 3 ≤ (Real.log ((⌊x⌋₊ : ℝ) + 1)) ^ 3 :=
      pow_le_pow_left₀ hlog.le hlognext 3
    have hcorr : 4 / (Real.log ((⌊x⌋₊ : ℝ) + 1)) ^ 3 ≤ 4 / (Real.log x) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    have hcert := TaoFivePrimes.mertens_reciprocal_endpoint_certificate_511 ⌊x⌋₊ hn hn511
    linarith
