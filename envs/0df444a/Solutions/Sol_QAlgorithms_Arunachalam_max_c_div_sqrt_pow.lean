-- Prove2me | solution 1 for QAlgorithms.Arunachalam.max_c_div_sqrt_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:36:28.340651+00:00
-- url     : https://prove2.me/submissions/072d87a4-2679-4bf9-b224-50a02e8a2048

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

private lemma log_ratio {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    Real.log (c / Real.sqrt t) =
      (1 + Real.log ((c ^ 2 / Real.exp 1) / t)) / 2 := by
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt (Real.sqrt_pos.2 ht)), Real.log_sqrt ht.le]
  rw [Real.log_div (ne_of_gt (div_pos (sq_pos_of_pos hc) (Real.exp_pos 1)))
    (ne_of_gt ht), Real.log_div (ne_of_gt (sq_pos_of_pos hc)) (ne_of_gt (Real.exp_pos 1)),
    Real.log_pow, Real.log_exp]
  ring

private lemma value_bound {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    (c / Real.sqrt t) ^ t ≤ Real.exp (c ^ 2 / (2 * Real.exp 1)) := by
  rw [Real.rpow_def_of_pos (div_pos hc (Real.sqrt_pos.2 ht))]
  apply Real.exp_le_exp.2
  rw [log_ratio hc ht]
  have hlog := Real.log_le_sub_one_of_pos (div_pos
    (div_pos (sq_pos_of_pos hc) (Real.exp_pos 1)) ht)
  have hmul := mul_le_mul_of_nonneg_right hlog ht.le
  have hcancel : ((c ^ 2 / Real.exp 1) / t) * t = c ^ 2 / Real.exp 1 :=
    div_mul_cancel₀ _ (ne_of_gt ht)
  rw [sub_mul, hcancel] at hmul
  have hn : c ^ 2 / (2 * Real.exp 1) = (c ^ 2 / Real.exp 1) / 2 := by ring
  rw [hn]
  nlinarith

private lemma value_attained {c : ℝ} (hc : 0 < c) :
    (c / Real.sqrt (c ^ 2 / Real.exp 1)) ^ (c ^ 2 / Real.exp 1) =
      Real.exp (c ^ 2 / (2 * Real.exp 1)) := by
  have ha : 0 < c ^ 2 / Real.exp 1 := div_pos (sq_pos_of_pos hc) (Real.exp_pos 1)
  rw [Real.rpow_def_of_pos (div_pos hc (Real.sqrt_pos.2 ha)), log_ratio hc ha,
    div_self (ne_of_gt ha), Real.log_one]
  congr 1
  ring

theorem solution {c : ℝ} (hc : Real.sqrt (Real.exp 1) ≤ c) :
    IsGreatest ((fun t : ℝ => (c / Real.sqrt t) ^ t) '' Set.Icc 1 (c ^ 2))
      (Real.exp (c ^ 2 / (2 * Real.exp 1))) := by
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hc0 : 0 < c := lt_of_lt_of_le (Real.sqrt_pos.2 he) hc
  have hsq : Real.exp 1 ≤ c ^ 2 := by
    nlinarith [Real.sq_sqrt he.le, Real.sqrt_nonneg (Real.exp 1)]
  have he1 : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  constructor
  · refine ⟨c ^ 2 / Real.exp 1, ⟨?_, ?_⟩, value_attained hc0⟩
    · exact (le_div_iff₀ he).2 (by simpa using hsq)
    · exact div_le_self (sq_nonneg c) he1
  · rintro _ ⟨t, ht, rfl⟩
    exact value_bound hc0 (lt_of_lt_of_le zero_lt_one ht.1)
