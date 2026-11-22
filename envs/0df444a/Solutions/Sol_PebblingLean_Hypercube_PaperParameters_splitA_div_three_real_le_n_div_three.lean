-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitA_div_three_real_le_n_div_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:25.689248+00:00
-- url     : https://prove2.me/submissions/fed7abca-9dff-4558-803b-e87e30ae005f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_real_le_n
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_div_real_le_div

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ} :
    ((splitA K n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
  have hdiv_le :
      ((splitA K n / 3 : ℕ) : ℝ) ≤ (splitA K n : ℝ) / 3 :=
    nat_div_real_le_div (splitA K n) 3 (by decide)
  have hsplitA_le_n := splitA_real_le_n (K := K) (n := n)
  linarith
end PebblingLean.Hypercube.PaperParameters
