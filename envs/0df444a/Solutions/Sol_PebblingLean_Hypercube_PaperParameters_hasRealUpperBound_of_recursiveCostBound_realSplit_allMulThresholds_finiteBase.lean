-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_realSplit_allMulThresholds_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:43:24.80697+00:00
-- url     : https://prove2.me/submissions/290b7545-0c46-49f6-903b-36bccd6ea842

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_two_le_splitA_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_real_le_quarter
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_ceilingSq_of_pow_half
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_allMulThresholds_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {lamLeft lamRight : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hsplitReal :
      ∀ n : ℕ, n0 ≤ n → (splitM K n : ℝ) ≤ (n : ℝ) / 4)
    (hlamLeft :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamLeft n)
    (hlamRight :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamRight n)
    (hleftMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * leftChernoffTerm A K lamLeft n ≤ loss n)
    (hrightMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * rightChernoffTerm A K lamRight n ≤ loss n)
    (hlogWidthMul :
      ∀ n : ℕ, n0 ≤ n →
        128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
            (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ))
    (hstackMul :
      ∀ n : ℕ, n0 ≤ n →
        2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
          (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilHalf :
      ∀ n : ℕ, n0 ≤ n →
        (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2))) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_allMulThresholds_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    (fun n hn => four_mul_splitM_le_of_real_le_quarter (hsplitReal n hn))
    hlamLeft
    hlamRight
    hleftMul
    hrightMul
    hlogWidthMul
    hstackMul
    (fun n hn =>
      ceilingSq_of_pow_half
        (n_div_two_le_splitA_of_four_mul_le
          (four_mul_splitM_le_of_real_le_quarter (hsplitReal n hn)))
        (hceilHalf n hn))
end PebblingLean.Hypercube.PaperParameters
