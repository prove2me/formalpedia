-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.rIn_real_le_third_sub_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:10.186811+00:00
-- url     : https://prove2.me/submissions/4206b855-ce6a-4665-bdb8-0c6732e0caf4

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_div_real_le_div

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hcenter : annulusWidth A K n ≤ splitA K n / 3) :
    (rIn A K n : ℝ) ≤
      (splitA K n : ℝ) / 3 - (annulusWidth A K n : ℝ) := by
  unfold rIn
  rw [Nat.cast_sub hcenter]
  have hdiv :=
    nat_div_real_le_div (splitA K n) 3 (by decide : 0 < 3)
  linarith
end PebblingLean.Hypercube.PaperParameters
