-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_lemma15_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T09:18:03.31015+00:00
-- url     : https://prove2.me/submissions/18d8948a-66d2-4c33-8ed6-38bc025638fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_theorem33
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound
import Theorems.Thm_TaoFivePrimes_euler_mascheroni_exp_bound

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace TaoFivePrimes

/-- Rosser–Schoenfeld (1962), Lemma 15 with the constant `288`. -/
theorem solution (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 288 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have h33h : (n : ℝ) < Real.exp (Chebyshev.theta (Real.log (n : ℝ) + y)) := by
    have h := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log hnpos] at h
  have h33 := rosser_schoenfeld_totient_theorem33 (Real.log (n : ℝ) + y) n
    (by linarith) (by omega) h33h
  have hPB := rosser_schoenfeld_product_bound (Real.log (n : ℝ) + y - 2) (by linarith)
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := by
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hneg : 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) < 0 :=
        div_neg_of_pos_of_neg (by linarith) hlt
      linarith
    · have hlog_ge : (286 : ℝ) ≤ Real.log (n : ℝ) := by
        rw [heq, div_zero] at h4
        linarith
      have hpos286 : (0 : ℝ) < Real.log (286 : ℝ) := Real.log_pos (by norm_num)
      have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 286) hlog_ge
      rw [heq] at hmono
      linarith
  have ht : (y - 2) / Real.log (n : ℝ) ≤ 0.9 / Real.log (Real.log (n : ℝ)) := by
    rw [div_le_div_iff₀ hlogpos hLpos]
    have h := (le_div_iff₀ hLpos).mp h4
    linarith
  have h1t : (0 : ℝ) < 1 + (y - 2) / Real.log (n : ℝ) := by
    have h : 0 ≤ (y - 2) / Real.log (n : ℝ) := div_nonneg h3 hlogpos.le
    linarith
  have hmul : Real.log (n : ℝ) * (1 + (y - 2) / Real.log (n : ℝ)) =
      Real.log (n : ℝ) + y - 2 := by
    field_simp
    ring
  have hxm_decomp : Real.log (Real.log (n : ℝ) + y - 2) =
      Real.log (Real.log (n : ℝ)) + Real.log (1 + (y - 2) / Real.log (n : ℝ)) := by
    rw [← hmul, Real.log_mul hlogpos.ne' h1t.ne']
  have hlog1t : Real.log (1 + (y - 2) / Real.log (n : ℝ)) ≤
      (y - 2) / Real.log (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos h1t
    linarith
  have hlogxm_le : Real.log (Real.log (n : ℝ) + y - 2) ≤
      Real.log (Real.log (n : ℝ)) + 0.9 / Real.log (Real.log (n : ℝ)) := by
    rw [hxm_decomp]
    linarith
  have hlogxm_pos : 0 < Real.log (Real.log (n : ℝ) + y - 2) := by
    apply Real.log_pos
    linarith
  have hrec : 1 / (2 * Real.log (Real.log (n : ℝ) + y - 2)) ≤
      0.5 / Real.log (Real.log (n : ℝ)) := by
    rw [show (0.5 : ℝ) / Real.log (Real.log (n : ℝ)) =
      1 / (2 * Real.log (Real.log (n : ℝ))) by ring]
    apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 2 * Real.log (Real.log (n : ℝ)))
    have h := Real.log_le_log hlogpos (by linarith : Real.log (n : ℝ) ≤ Real.log (n : ℝ) + y - 2)
    linarith
  have hsum : Real.log (Real.log (n : ℝ) + y - 2) +
        1 / (2 * Real.log (Real.log (n : ℝ) + y - 2)) ≤
      Real.log (Real.log (n : ℝ)) + 1.4 / Real.log (Real.log (n : ℝ)) :=
    calc Real.log (Real.log (n : ℝ) + y - 2) +
          1 / (2 * Real.log (Real.log (n : ℝ) + y - 2))
        ≤ (Real.log (Real.log (n : ℝ)) + 0.9 / Real.log (Real.log (n : ℝ))) +
            0.5 / Real.log (Real.log (n : ℝ)) := add_le_add hlogxm_le hrec
      _ = Real.log (Real.log (n : ℝ)) + 1.4 / Real.log (Real.log (n : ℝ)) := by
          ring
  calc (n : ℝ) / Nat.totient n
      ≤ ∏ p ∈ Nat.primesLE ⌊Real.log (n : ℝ) + y - 2⌋₊,
          (p : ℝ) / ((p : ℝ) - 1) := h33
    _ < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ) + y - 2) *
          (1 + 1 / (2 * (Real.log (Real.log (n : ℝ) + y - 2)) ^ 2)) := hPB
    _ = Real.exp Real.eulerMascheroniConstant *
          (Real.log (Real.log (n : ℝ) + y - 2) +
            1 / (2 * Real.log (Real.log (n : ℝ) + y - 2))) := by
        have hne : Real.log (Real.log (n : ℝ) + y - 2) ≠ 0 := hlogxm_pos.ne'
        field_simp
    _ ≤ Real.exp Real.eulerMascheroniConstant *
          (Real.log (Real.log (n : ℝ)) + 1.4 / Real.log (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
          5 / (2 * Real.log (Real.log (n : ℝ))) := by
        rw [mul_add]
        have hγ := euler_mascheroni_exp_bound
        have hnum : Real.exp Real.eulerMascheroniConstant * 1.4 ≤ 2.5 := by nlinarith
        have hstep : Real.exp Real.eulerMascheroniConstant *
            (1.4 / Real.log (Real.log (n : ℝ))) ≤
            5 / (2 * Real.log (Real.log (n : ℝ))) := by
          rw [← mul_div_assoc,
            show (5 : ℝ) / (2 * Real.log (Real.log (n : ℝ))) =
              2.5 / Real.log (Real.log (n : ℝ)) by ring]
          exact div_le_div_of_nonneg_right hnum hLpos.le
        linarith

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 288 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) :=
  TaoFivePrimes.solution n y hn h1 h2 h3 h4
