-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T08:37:00.606667+00:00
-- url     : https://prove2.me/submissions/03ecf56b-ca0e-4dae-94e2-46718bd7577f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_pointwise

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_totient_bound`

The target is the uniformized form of Rosser–Schoenfeld (1962), Theorem 15,
used by Tao in the proof of Proposition 4.10 (arXiv:1201.6656): for every
odd `n ≤ H` with `H ≥ 10²`,

`2n/φ(2n) ≤ e^γ log log (2H) + 2.507 / log log (2H)`.

The reduction proceeds from the pointwise child
`TaoFivePrimes.rosser_schoenfeld_totient_pointwise` (Theorem 15 with the
uniform constant `2.50637`):

* `n ≤ 15`: direct verification, `2n/φ(2n) ≤ 3.75`, while the target's
  right-hand side is `≥ e^{1/2}·1.6 + 2.507/1.6 ≥ 4.2` because
  `log log (2H) ≥ log log 200 ≥ 1.6` for `H ≥ 100`;
* `n ≥ 17` (odd): the pointwise bound at `2n` is compared with the value at
  `2H` using `u = log log (2n) ≥ log log 34 ≥ 1.25`,
  `v = log log (2H) ≥ u` and the algebraic identity
  `(e^γ v + c/v) - (e^γ u + c/u) = (v-u)(e^γ - c/(uv))`,
  where `c/(uv) ≤ 2.507/(1.25·1.25) ≤ e^γ`.

All numerical inputs are elementary: `1/2 < γ < 2/3` (Mathlib), the Taylor
bound `Real.exp_bound'` for `exp` on `[0,1]`, and the decimal bounds
`Real.exp_one_lt_d9`, `Real.log_two_gt_d9`, `Real.log_five_gt_d9`.
-/

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_bound_proof (H n : ℕ) (hH : 10 ^ 2 ≤ H)
    (hn : n % 2 = 1) (hnH : n ≤ H) :
    (2 * n : ℝ) / Nat.totient (2 * n) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (2 * (H : ℝ))) +
        2.507 / Real.log (Real.log (2 * (H : ℝ))) := by
  -- e^γ ≥ e^{1/2} ≥ 1.64872
  have hγ : (1.64872 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    have hhalf : (1.64872 : ℝ) ≤ Real.exp (1 / 2) := by
      by_contra h
      rw [not_le] at h
      have hsq : (Real.exp (1 / 2)) ^ 2 < 1.64872 ^ 2 := by
        apply pow_lt_pow_left₀ h (Real.exp_pos _).le
        norm_num
      have heq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
        rw [pow_two, ← Real.exp_add]
        norm_num
      rw [heq] at hsq
      linarith [Real.exp_one_gt_d9]
    exact hhalf.trans
      (Real.exp_le_exp.mpr (le_of_lt Real.one_half_lt_eulerMascheroniConstant))
  -- e^{1/4} ≤ 1.285
  have h025 : Real.exp (1 / 4) ≤ 1.285 := by
    have h := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  -- e^{5/4} ≤ 3.5
  have hexp125 : Real.exp 1.25 ≤ 3.5 := by
    rw [show (1.25 : ℝ) = 1 + 1 / 4 by norm_num, Real.exp_add]
    calc Real.exp 1 * Real.exp (1 / 4) ≤ 2.7182818286 * 1.285 :=
          mul_le_mul Real.exp_one_lt_d9.le h025 (Real.exp_pos _).le (by norm_num)
      _ ≤ 3.5 := by norm_num
  -- e^3 ≤ 20.0856
  have h3 : Real.exp 3 ≤ 20.0856 := by
    have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    have hp : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    calc Real.exp 1 * Real.exp 1 * Real.exp 1 ≤
          2.7182818286 * 2.7182818286 * 2.7182818286 := by
          apply mul_le_mul (mul_le_mul he he hp (by norm_num)) he hp (by norm_num)
      _ ≤ 20.0856 := by norm_num
  -- e^{1/2} ≤ 1.6490886
  have h05 : Real.exp (1 / 2) ≤ 1.6490886 := by
    have h := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  -- log 34 ≥ 3.5
  have hlog34 : (3.5 : ℝ) ≤ Real.log 34 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    rw [show (3.5 : ℝ) = 3 + 1 / 2 by norm_num, Real.exp_add]
    calc Real.exp 3 * Real.exp (1 / 2) ≤ 20.0856 * 1.6490886 :=
          mul_le_mul h3 h05 (Real.exp_pos _).le (by norm_num)
      _ ≤ 34 := by norm_num
  -- e^{3/5} ≤ 1.828
  have h06 : Real.exp (3 / 5) ≤ 1.828 := by
    have h := Real.exp_bound' (x := 3 / 5) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    linarith
  -- log 200 ≥ 5.2983173
  have hlog200 : (5.2983173 : ℝ) ≤ Real.log 200 := by
    have h : Real.log 200 = 3 * Real.log 2 + 2 * Real.log 5 := by
      rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num)
        (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [h]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  -- log log 200 ≥ 1.6
  have hloglog200 : (1.6 : ℝ) ≤ Real.log (Real.log 200) := by
    rw [Real.le_log_iff_exp_le (by linarith [hlog200])]
    calc Real.exp 1.6 = Real.exp 1 * Real.exp (3 / 5) := by
          rw [show (1.6 : ℝ) = 1 + 3 / 5 by norm_num, Real.exp_add]
      _ ≤ 2.7182818286 * 1.828 :=
          mul_le_mul Real.exp_one_lt_d9.le h06 (Real.exp_pos _).le (by norm_num)
      _ ≤ 5.2983173 := by norm_num
      _ ≤ Real.log 200 := hlog200
  -- 2H ≥ 200 and log log (2H) ≥ 1.6
  have h2H200 : (200 : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast (show 200 ≤ 2 * H by omega)
  have hloglog2H : (1.6 : ℝ) ≤ Real.log (Real.log (2 * (H : ℝ))) := by
    have h1 : Real.log 200 ≤ Real.log (2 * (H : ℝ)) := Real.log_le_log (by norm_num) h2H200
    exact hloglog200.trans (Real.log_le_log (by linarith [hlog200]) h1)
  -- log log 34 ≥ 1.25
  have hloglog34 : (1.25 : ℝ) ≤ Real.log (Real.log 34) := by
    rw [Real.le_log_iff_exp_le (by linarith [hlog34])]
    exact hexp125.trans hlog34
  -- the comparison `e^γ u + c/u ≤ e^γ v + c/v` for `0 < u ≤ v` and `c/(uv) ≤ e^γ`
  have mon : ∀ {u v : ℝ}, 0 < u → u ≤ v →
      2.507 / (u * v) ≤ Real.exp Real.eulerMascheroniConstant →
      Real.exp Real.eulerMascheroniConstant * u + 2.507 / u ≤
        Real.exp Real.eulerMascheroniConstant * v + 2.507 / v := by
    intro u v hu0 huv hc
    have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
    rw [← sub_nonneg]
    have e : (Real.exp Real.eulerMascheroniConstant * v + 2.507 / v) -
        (Real.exp Real.eulerMascheroniConstant * u + 2.507 / u) =
        (v - u) * (Real.exp Real.eulerMascheroniConstant - 2.507 / (u * v)) := by
      field_simp
      ring
    rw [e]
    exact mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hc)
  by_cases hn15 : n ≤ 15
  · -- small cases: `2n/φ(2n) ≤ 3.75 ≤ e^{1/2}·1.6 + 2.507/1.6 ≤ e^γ v + 2.507/v`
    have hnat : 8 * n ≤ 15 * Nat.totient (2 * n) := by interval_cases n <;> decide
    have hφ2n : 0 < 2 * n := by omega
    have hφ : (0 : ℝ) < Nat.totient (2 * n) := by
      exact_mod_cast (Nat.totient_pos.mpr hφ2n : 0 < Nat.totient (2 * n))
    have hsmall : (2 * n : ℝ) / Nat.totient (2 * n) ≤ 3.75 := by
      rw [div_le_iff₀ hφ]
      have : (8 * n : ℝ) ≤ 15 * (Nat.totient (2 * n) : ℝ) := by exact_mod_cast hnat
      linarith
    have hmon16 : Real.exp Real.eulerMascheroniConstant * 1.6 + 2.507 / 1.6 ≤
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (2 * (H : ℝ))) +
          2.507 / Real.log (Real.log (2 * (H : ℝ))) := by
      apply mon (by norm_num) hloglog2H
      have hden : (1.6 : ℝ) * 1.6 ≤ 1.6 * Real.log (Real.log (2 * (H : ℝ))) := by
        nlinarith
      calc 2.507 / (1.6 * Real.log (Real.log (2 * (H : ℝ)))) ≤ 2.507 / (1.6 * 1.6) :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
        _ ≤ 1.64872 := by norm_num
        _ ≤ Real.exp Real.eulerMascheroniConstant := hγ
    have hF16 : (3.75 : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * 1.6 + 2.507 / 1.6 := by
      have h16 : (1.64872 : ℝ) * 1.6 ≤ Real.exp Real.eulerMascheroniConstant * 1.6 :=
        mul_le_mul_of_nonneg_right hγ (by norm_num)
      linarith
    linarith
  · -- large cases: pointwise bound at `2n`, compared with the value at `2H`
    have hn17 : 17 ≤ n := by omega
    have hchild := rosser_schoenfeld_totient_pointwise (2 * n) (by omega)
    have h2n34 : (34 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show 34 ≤ 2 * n by omega)
    have hlog2n : Real.log 34 ≤ Real.log ((2 * n : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) h2n34
    have hu : (1.25 : ℝ) ≤ Real.log (Real.log ((2 * n : ℕ) : ℝ)) :=
      hloglog34.trans (Real.log_le_log (by linarith [hlog34]) hlog2n)
    have h2Hn : ((2 * n : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
      exact_mod_cast (show 2 * n ≤ 2 * H by omega)
    have huv : Real.log (Real.log ((2 * n : ℕ) : ℝ)) ≤
        Real.log (Real.log (2 * (H : ℝ))) :=
      Real.log_le_log (by linarith [hlog34, hlog2n])
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * n)) h2Hn)
    have hu0 : 0 < Real.log (Real.log ((2 * n : ℕ) : ℝ)) := by linarith
    have hc : 2.507 / (Real.log (Real.log ((2 * n : ℕ) : ℝ)) *
        Real.log (Real.log (2 * (H : ℝ)))) ≤ Real.exp Real.eulerMascheroniConstant := by
      have huv' : (1.5625 : ℝ) ≤ Real.log (Real.log ((2 * n : ℕ) : ℝ)) *
          Real.log (Real.log (2 * (H : ℝ))) := by nlinarith
      calc 2.507 / (Real.log (Real.log ((2 * n : ℕ) : ℝ)) *
            Real.log (Real.log (2 * (H : ℝ)))) ≤ 2.507 / 1.5625 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) huv'
        _ ≤ 1.64872 := by norm_num
        _ ≤ Real.exp Real.eulerMascheroniConstant := hγ
    have hmon := mon hu0 huv hc
    have h506 : 2.50637 / Real.log (Real.log ((2 * n : ℕ) : ℝ)) ≤
        2.507 / Real.log (Real.log ((2 * n : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right (by norm_num) hu0.le
    have key : ((2 * n : ℕ) : ℝ) / Nat.totient (2 * n) ≤
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (2 * (H : ℝ))) +
          2.507 / Real.log (Real.log (2 * (H : ℝ))) := by linarith
    have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
    rwa [hcast] at key

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (H n : ℕ) (hH : 10 ^ 2 ≤ H) (hn : n % 2 = 1) (hnH : n ≤ H) :
    (2 * n : ℝ) / Nat.totient (2 * n) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (2 * (H : ℝ))) +
        2.507 / Real.log (Real.log (2 * (H : ℝ))) :=
  TaoFivePrimes.rosser_schoenfeld_totient_bound_proof H n hH hn hnH

#print axioms solution
