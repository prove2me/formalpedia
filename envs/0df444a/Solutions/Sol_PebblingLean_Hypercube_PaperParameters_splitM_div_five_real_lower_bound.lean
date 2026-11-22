-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitM_div_five_real_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:05.001827+00:00
-- url     : https://prove2.me/submissions/2baade3a-83c2-4cdb-9d40-7c2c32966b5c

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_core_le_real

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ} :
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1 ≤
      ((splitM K n / 5 : ℕ) : ℝ) := by
  have hcore := splitM_core_le_real (K := K) (n := n)
  have hfloor :
      (splitM K n : ℝ) / 5 - 1 ≤ ((splitM K n / 5 : ℕ) : ℝ) := by
    have hnat : splitM K n < 5 * (splitM K n / 5 + 1) :=
      Nat.lt_mul_div_succ (splitM K n) (by decide : 0 < 5)
    have hreal : (splitM K n : ℝ) < (5 * (splitM K n / 5 + 1) : ℕ) := by
      exact_mod_cast hnat
    norm_num at hreal
    linarith
  have hdiv :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 ≤
        (splitM K n : ℝ) / 5 :=
    div_le_div_of_nonneg_right hcore (by norm_num : (0 : ℝ) ≤ 5)
  linarith
end PebblingLean.Hypercube.PaperParameters
