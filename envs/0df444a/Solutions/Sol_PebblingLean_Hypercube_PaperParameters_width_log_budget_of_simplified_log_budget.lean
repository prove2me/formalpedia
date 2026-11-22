-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_log_budget_of_simplified_log_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:21.221101+00:00
-- url     : https://prove2.me/submissions/af35b8fe-19e1-46a7-9097-b02d8a24c6ee

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_succ_mul_log_two_le_log_succ
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_succ_le_log_two_add_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hbudget :
      Real.log 128 + 4 * Real.log 2 + 5 * Real.log (n : ℝ) ≤
        (K / 15 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 3 * Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
        4 * Real.log (n : ℝ) ≤
      (K / 15 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hmiddle :
      Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        Real.log 2 + Real.log (n : ℝ) :=
    log_succ_mul_log_two_le_log_succ.trans
      (log_succ_le_log_two_add_log (n := n) hn)
  have hcoarse :
      Real.log 128 + 3 * Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
          4 * Real.log (n : ℝ) ≤
        Real.log 128 + 4 * Real.log 2 + 5 * Real.log (n : ℝ) := by
    linarith
  exact hcoarse.trans hbudget
end PebblingLean.Hypercube.PaperParameters
