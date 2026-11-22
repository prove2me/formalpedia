-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_coarse_of_sqrt_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:22.811808+00:00
-- url     : https://prove2.me/submissions/e84dd955-1ad2-4b7d-b340-c981727868d7

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
      Real.log 128 + 3 * Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
          4 * Real.log (n : ℝ) ≤
        ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + (2 *
        (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
        Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      -4 * Real.log (n : ℝ) +
        (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
          Real.log 2 := by
  rw [sqrt_three_n_log_eq n]
  ring_nf at hmargin ⊢
  linarith
end PebblingLean.Hypercube.PaperParameters
