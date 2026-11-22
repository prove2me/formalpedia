-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:32.60564+00:00
-- url     : https://prove2.me/submissions/6dc6af5a-0f83-4de3-b441-a9c04dc65da0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_ge_of_core_ge
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_chernoff_width_sq_of_core_sq
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_width_le_splitA_of_core_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffWidthSq_finiteBase

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
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hthreeWidthCore :
      ∀ n : ℕ, n0 ≤ n →
        3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ))
    (hwidthCoreNine :
      ∀ n : ℕ, n0 ≤ n →
        9 ≤ annulusWidthCore A K n)
    (hchernoffCoreSq :
      ∀ n : ℕ, n0 ≤ n →
        12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
          (annulusWidthCore A K n) ^ 2)
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffWidthSq_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hn0_growth
    hK
    hA
    hKdom
    hKlarge
    hsplitThreshold
    (fun n hn =>
      three_width_le_splitA_of_core_bound
        (A := A) (K := K) (n := n)
        hA
        (hthreeWidthCore n hn))
    (fun n hn =>
      annulusWidth_real_ge_of_core_ge
        (A := A) (K := K) (n := n)
        (hwidthCoreNine n hn))
    (fun n hn =>
      chernoff_width_sq_of_core_sq
        (A := A) (K := K) (n := n)
        hA
        (hchernoffCoreSq n hn))
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
