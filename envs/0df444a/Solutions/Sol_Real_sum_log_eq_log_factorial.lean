-- Prove2me | solution 1 for Real.sum_log_eq_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:59.925725+00:00
-- url     : https://prove2.me/submissions/b2b28cc7-3622-49bf-9226-60dac5029ae1

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
theorem _root_.solution : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  rw [← prod_Ico_id_eq_factorial, ← log_prod (by intros; simp; grind), prod_natCast]
  rfl
end Real
