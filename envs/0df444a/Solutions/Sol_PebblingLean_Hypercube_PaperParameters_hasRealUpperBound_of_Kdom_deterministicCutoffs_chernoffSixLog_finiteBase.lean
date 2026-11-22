-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffSixLog_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:02:45.289815+00:00
-- url     : https://prove2.me/submissions/5083be91-060f-42ae-8ee8-a54d811835fd

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusChernoffLambda_le_one_of_three_width_le_splitA
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffWidthExponent_finiteBase

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
    (hthreeWidth :
      ∀ n : ℕ, n0 ≤ n →
        3 * annulusWidth A K n ≤ splitA K n)
    (hwidthNine :
      ∀ n : ℕ, n0 ≤ n →
        9 ≤ (annulusWidth A K n : ℝ))
    (hchernoffSix :
      ∀ n : ℕ, n0 ≤ n →
        6 * Real.log (n : ℝ) ≤
          (1 / 2) *
            ((annulusWidth A K n : ℝ) ^ 2 /
              ((splitA K n : ℝ) + 1)))
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
  hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffWidthExponent_finiteBase
    (K := K) (A := A) (n0 := n0)
    (tailExponent := fun n => 6 * Real.log (n : ℝ))
    hn0_pos
    hn0_growth
    hK
    hA
    hKdom
    hKlarge
    hsplitThreshold
    (fun n hn => by
      have h := hthreeWidth n hn
      omega)
    hwidthNine
    (fun n hn =>
      annulusChernoffLambda_le_one_of_three_width_le_splitA
        (A := A) (K := K) (n := n)
        (hthreeWidth n hn))
    hchernoffSix
    (fun _n _hn => le_rfl)
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
