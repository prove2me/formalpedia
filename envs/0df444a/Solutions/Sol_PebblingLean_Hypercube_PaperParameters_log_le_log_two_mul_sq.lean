-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.log_le_log_two_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:29.801434+00:00
-- url     : https://prove2.me/submissions/6518021c-dbd3-407b-a233-b9ea8ee72c92

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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ) ^ 2) := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact Real.log_le_log hn_pos hle
end PebblingLean.Hypercube.PaperParameters
