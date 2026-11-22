-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_Knonneg_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:52.549067+00:00
-- url     : https://prove2.me/submissions/bdba1b82-6db8-4c17-9916-a91b5612828d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_real_le_quarter
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_real_le_quarter_of_ceiling_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_core_nonneg_of_K_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_core_bound_of_log_le_linear
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_log_budget_of_quadratic_threshold

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K : ℝ} {n0 n : ℕ}
    (hK : 0 ≤ K)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hn : n0 ≤ n) :
    4 * splitM K n ≤ n := by
  have hnreal : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogLinear :
      K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64 :=
    split_log_budget_of_quadratic_threshold
      (K := K) (n := n)
      (hsplitThreshold.trans hnreal)
  have hcore :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
        (n : ℝ) / 4 :=
    split_core_bound_of_log_le_linear
      (K := K) (n := n)
      hK
      (by omega : 8 ≤ n)
      hlogLinear
  exact four_mul_splitM_le_of_real_le_quarter
    (splitM_real_le_quarter_of_ceiling_bound
      (splitM_core_nonneg_of_K_nonneg hK)
      hcore)
end PebblingLean.Hypercube.PaperParameters
