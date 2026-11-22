-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_standardLambda_allMulThresholds_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:44:20.585798+00:00
-- url     : https://prove2.me/submissions/f29bfa99-01aa-49f7-bee6-8e89fca4dc95

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusChernoffLambda_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_realSplit_allMulThresholds_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hsplitReal :
      ∀ n : ℕ, n0 ≤ n → (splitM K n : ℝ) ≤ (n : ℝ) / 4)
    (hleftMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * leftChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
    (hrightMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * rightChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
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
  hasRealUpperBound_of_recursiveCostBound_realSplit_allMulThresholds_finiteBase
    (K := K) (A := A) (n0 := n0)
    (lamLeft := annulusChernoffLambda A K)
    (lamRight := annulusChernoffLambda A K)
    hn0_pos
    hsplitReal
    (fun n _hn => annulusChernoffLambda_nonneg A K n)
    (fun n _hn => annulusChernoffLambda_nonneg A K n)
    hleftMul
    hrightMul
    hlogWidthMul
    hstackMul
    hceilHalf
end PebblingLean.Hypercube.PaperParameters
