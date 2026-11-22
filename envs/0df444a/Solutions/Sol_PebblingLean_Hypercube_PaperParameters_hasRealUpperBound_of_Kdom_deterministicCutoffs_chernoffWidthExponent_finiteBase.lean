-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffWidthExponent_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:29.198377+00:00
-- url     : https://prove2.me/submissions/75cf5777-8dbf-4f2f-807c-5c1abb522f1f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_left_standard_chernoff_log_le_of_width_exponent
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_right_standard_chernoff_log_le_of_width_exponent
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_logChernoff_sixLog_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hcenter :
      ∀ n : ℕ, n0 ≤ n →
        annulusWidth A K n ≤ splitA K n / 3)
    (hwidthNine :
      ∀ n : ℕ, n0 ≤ n →
        9 ≤ (annulusWidth A K n : ℝ))
    (hlambdaOne :
      ∀ n : ℕ, n0 ≤ n →
        annulusChernoffLambda A K n ≤ 1)
    (hchernoffExponent :
      ∀ n : ℕ, n0 ≤ n →
        tailExponent n ≤
          (1 / 2) *
            ((annulusWidth A K n : ℝ) ^ 2 /
              ((splitA K n : ℝ) + 1)))
    (htailSix :
      ∀ n : ℕ, n0 ≤ n →
        6 * Real.log (n : ℝ) ≤ tailExponent n)
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
  hasRealUpperBound_of_Kdom_deterministicCutoffs_logChernoff_sixLog_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hKdom
    hKlarge
    hsplitThreshold
    (fun n hn =>
      left_standard_chernoff_log_le_of_width_exponent
        (A := A) (K := K) (n := n) (E := tailExponent n)
        (hcenter n hn)
        (hlambdaOne n hn)
        (by
          have hcore :
              0 ≤ (annulusWidth A K n : ℝ) ^ 2 /
                ((splitA K n : ℝ) + 1) := by
            positivity
          nlinarith [hchernoffExponent n hn, hcore]))
    (fun n hn =>
      right_standard_chernoff_log_le_of_width_exponent
        (A := A) (K := K) (n := n) (E := tailExponent n)
        (hwidthNine n hn)
        (hlambdaOne n hn)
        (hchernoffExponent n hn))
    htailSix
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
