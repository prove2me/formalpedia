-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_margin_of_sqrt_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:28.729922+00:00
-- url     : https://prove2.me/submissions/495cbb25-8be6-4f04-87ad-8e52f807dfc6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sqrt_three_n_log_eq

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hmargin :
      2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
        ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
          Real.log 2 ≤
      (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
          Real.log 2 +
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  rw [sqrt_three_n_log_eq n]
  ring_nf at hmargin ⊢
  linarith
end PebblingLean.Hypercube.PaperParameters
