-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:10.314805+00:00
-- url     : https://prove2.me/submissions/55a2abfa-75e6-4c7f-b604-64b914948a6a

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_explicitConstants_mainCutoffs_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_coreNineCutoff_of_splitThreshold
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_widthConstCutoff_of_splitThreshold
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_stackLogThreshold_of_splitThreshold
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_stackConstCutoff_of_splitThreshold

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
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound 217 n0) n0) :=
  hasRealUpperBound_of_explicitConstants_mainCutoffs_finiteBase
    (n0 := n0)
    hn0_pos
    hn0_growth
    hsplitThreshold
    (explicit_coreNineCutoff_of_splitThreshold
      (n0 := n0) hsplitThreshold)
    (explicit_widthConstCutoff_of_splitThreshold
      (n0 := n0) hsplitThreshold)
    (explicit_stackLogThreshold_of_splitThreshold
      (n0 := n0) hsplitThreshold)
    (explicit_stackConstCutoff_of_splitThreshold
      (n0 := n0) hsplitThreshold)
end PebblingLean.Hypercube.PaperParameters
