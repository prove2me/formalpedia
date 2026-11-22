-- Prove2me | solution 1 for Real.le_sum_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:35.9078+00:00
-- url     : https://prove2.me/submissions/1c8d33de-df13-45c7-8a2c-f54ad92e5063

module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SumIntegralComparisons
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport

set_option autoImplicit true
@[expose] public section
public section
open Nat hiding log log_pos
open Finset intervalIntegral MeasureTheory
open Real
variable {x : ℝ} (N : ℕ)
namespace Real
theorem _root_.solution (hx : 1 ≤ x) : x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log x := by
      have : x - ⌊x⌋₊ ≤ 1 := by linarith [lt_floor_add_one x]
      grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul]
      nlinarith [log_nonneg hx]
    _ ≤ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
      rify at this
      gcongr
      apply integral_mono_on (floor_le (by linarith)) (by simp) (by simp)
      grind [log_le_log_iff]
    _ = ∫ t in 1..⌊x⌋₊, log t := by
      rw [integral_symm _ ⌊x⌋₊, sub_neg_eq_add, integral_add_adjacent_intervals] <;>
      simp
    _ ≤ _ := by
      rw [← Icc_add_one_left_eq_Ioc, zero_add, ← add_sum_Ioc_eq_sum_Icc this, cast_one,
        log_one, ← Ico_add_one_add_one_eq_Ioc, zero_add, ← sum_Ico_add']
      exact_mod_cast ((strictMonoOn_log.mono (by grind)).monotoneOn.integral_le_sum_Ico this)
end Real
