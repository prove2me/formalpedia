-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.chernoff_six_log_of_width_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:43.185103+00:00
-- url     : https://prove2.me/submissions/1ec9becc-5159-4068-8f49-ab020318048e

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
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hwidthSq :
      12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
        (annulusWidth A K n : ℝ) ^ 2) :
    6 * Real.log (n : ℝ) ≤
      (1 / 2) *
        ((annulusWidth A K n : ℝ) ^ 2 /
          ((splitA K n : ℝ) + 1)) := by
  have hden_pos : 0 < (splitA K n : ℝ) + 1 := by positivity
  rw [show (1 / 2) *
        ((annulusWidth A K n : ℝ) ^ 2 / ((splitA K n : ℝ) + 1)) =
      (annulusWidth A K n : ℝ) ^ 2 /
        (2 * ((splitA K n : ℝ) + 1)) by
        field_simp [hden_pos.ne']]
  rw [le_div_iff₀ (by positivity : 0 < 2 * ((splitA K n : ℝ) + 1))]
  nlinarith
end PebblingLean.Hypercube.PaperParameters
