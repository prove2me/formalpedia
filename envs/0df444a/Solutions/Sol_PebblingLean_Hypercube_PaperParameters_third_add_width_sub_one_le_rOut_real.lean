-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.third_add_width_sub_one_le_rOut_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:27.58917+00:00
-- url     : https://prove2.me/submissions/c51d38b5-e3fa-4114-9c95-03d936301879

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_div_sub_one_le_nat_div_real

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ} :
    (splitA K n : ℝ) / 3 + (annulusWidth A K n : ℝ) - 1 ≤
      (rOut A K n : ℝ) := by
  unfold rOut
  rw [Nat.cast_add]
  have hdiv :=
    div_sub_one_le_nat_div_real (splitA K n) 3 (by decide : 0 < 3)
  linarith
end PebblingLean.Hypercube.PaperParameters
