-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:32.187453+00:00
-- url     : https://prove2.me/submissions/731043c5-4d69-4acc-a2db-86eab6515bb1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (annulusWidthCore A K n) ^ 2 =
      A ^ 2 * ((splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2)) := by
  have hlog_nonneg : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have harg : (1 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
    exact Real.log_nonneg harg
  have harg_nonneg :
      0 ≤ (splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2) :=
    mul_nonneg (by positivity) hlog_nonneg
  unfold annulusWidthCore
  rw [mul_pow, Real.sq_sqrt harg_nonneg]
end PebblingLean.Hypercube.PaperParameters
