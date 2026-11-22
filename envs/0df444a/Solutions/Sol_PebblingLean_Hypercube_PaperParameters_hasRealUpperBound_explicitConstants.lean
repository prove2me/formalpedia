-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_explicitConstants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:15.54481+00:00
-- url     : https://prove2.me/submissions/4937af8a-b3f9-42a9-b77d-215be5863e3b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicitCutoff_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicitCutoff_growth
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicitCutoff_splitThreshold

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss explicitCutoff) *
        finiteBaseNormalizedBound (recursiveCostBound 217 explicitCutoff)
          explicitCutoff) :=
  hasRealUpperBound_of_explicitConstants_splitCutoff_finiteBase
    (n0 := explicitCutoff)
    explicitCutoff_pos
    explicitCutoff_growth
    explicitCutoff_splitThreshold
end PebblingLean.Hypercube.PaperParameters
