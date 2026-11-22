-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_mainCutoffs_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:09:26.013805+00:00
-- url     : https://prove2.me/submissions/a3868527-4d5d-474e-ac0f-c77559ee30c4

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_widthFitThreshold_of_splitThreshold

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hcoreNineCutoff :
      81 ≤ (4 : ℝ) ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        ((217 : ℝ) / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound 217 n0) n0) :=
  hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
    (n0 := n0)
    hn0_pos
    hn0_growth
    hsplitThreshold
    (explicit_widthFitThreshold_of_splitThreshold
      (n0 := n0) hsplitThreshold)
    hcoreNineCutoff
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
