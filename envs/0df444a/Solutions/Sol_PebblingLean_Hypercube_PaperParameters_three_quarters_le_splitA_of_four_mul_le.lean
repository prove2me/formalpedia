-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.three_quarters_le_splitA_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:31.601832+00:00
-- url     : https://prove2.me/submissions/c42a73a1-17ab-4d46-9c71-b6ec5f453872

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_real_eq_sub_of_four_mul_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ) := by
  have hsplit := splitA_real_eq_sub_of_four_mul_le (K := K) (n := n) hquarter
  have hm : (splitM K n : ℝ) ≤ (n : ℝ) / 4 := by
    have hreal : ((4 * splitM K n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hquarter
    norm_num at hreal
    linarith
  rw [hsplit]
  linarith
end PebblingLean.Hypercube.PaperParameters
