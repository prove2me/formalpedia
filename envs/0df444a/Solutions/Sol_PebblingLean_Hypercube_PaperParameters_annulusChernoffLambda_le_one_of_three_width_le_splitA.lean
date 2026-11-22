-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_le_one_of_three_width_le_splitA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:42.576051+00:00
-- url     : https://prove2.me/submissions/17531a32-9648-4273-93d6-dd8d3aec3eae

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
theorem _root_.solution
    {A K : ℝ} {n : ℕ}
    (hwidth : 3 * annulusWidth A K n ≤ splitA K n) :
    annulusChernoffLambda A K n ≤ 1 := by
  unfold annulusChernoffLambda
  have hreal :
      (3 : ℝ) * (annulusWidth A K n : ℝ) ≤ (splitA K n : ℝ) := by
    exact_mod_cast hwidth
  have hden_pos : 0 < (splitA K n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hden_pos]
  linarith
end PebblingLean.Hypercube.PaperParameters
