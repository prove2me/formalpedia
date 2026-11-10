-- Prove2me | solution 1 for QEC.Coding.BDL26RZSupportedBoundary.parity_eq_region_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:42:27.490054+00:00
-- url     : https://prove2.me/submissions/affdfa5d-5d41-4923-916e-ae61527a8b6f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_eq_region_sum


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZSupportedBoundary
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26RZConcreteParity
open MultiscaleDecoder
open MultiscaleDecoder.RZCoarseGraining.RZCoarseGrainingData
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZSupportedBoundary
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (r : topSpace P S z) :
    parity P S z r = ∑ p ∈ blockRegion P S z, r.1 p := by
  exact blockParity_eq_region_sum P S r.1 z
end QEC.Coding.BDL26RZSupportedBoundary
