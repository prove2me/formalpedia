-- Prove2me | solution 1 for Real.sum_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:05.66327+00:00
-- url     : https://prove2.me/submissions/ba73f0db-1539-4d3d-9169-983c83721d72

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
theorem _root_.solution (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1 := by
  have aux1 : ⌊x⌋₊ ≤ x := floor_le (by linarith)
  have aux2 : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in (1 : ℕ)..⌊x⌋₊, log t) + log x := by
      rw [← Icc_add_one_left_eq_Ioc, ← sum_Ico_add_eq_sum_Icc (by simpa)]
      gcongr
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico aux2
    _ ≤ (∫ t in 1..x, log t) + log x := by
      grw [Nat.cast_one, integral_mono_interval le_rfl (mod_cast aux2) aux1 _ (by simp)]
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun _ hy ↦ (log_nonneg hy.1.le)
    _ = _ := by grind [integral_log, log_one]
end Real
