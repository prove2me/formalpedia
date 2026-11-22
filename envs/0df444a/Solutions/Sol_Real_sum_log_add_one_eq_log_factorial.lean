-- Prove2me | solution 1 for Real.sum_log_add_one_eq_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:40.706034+00:00
-- url     : https://prove2.me/submissions/8762e749-b028-42b5-a5fb-1885dbee0ee2

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
theorem _root_.solution : ∑ n ∈ range N, log (n + 1) = log N.factorial := by
  rw [Nat.factorial_eq_prod_range_add_one, prod_natCast, log_prod (fun i _ ↦ by positivity)]
  push_cast
  rfl
end Real
