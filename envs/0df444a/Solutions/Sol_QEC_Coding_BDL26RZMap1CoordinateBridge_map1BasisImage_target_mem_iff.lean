-- Prove2me | solution 1 for QEC.Coding.BDL26RZMap1CoordinateBridge.map1BasisImage_target_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:18:22.609239+00:00
-- url     : https://prove2.me/submissions/e20f6c15-660b-416b-94ab-3949eae462fa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u
namespace QEC.Coding.BDL26RZMap1CoordinateBridge
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) (target : RZQ P S) :
    target ∈ rzMap1ParentRegion P A4 S q ↔
      map1BasisImage P A4 S q target ≠ 0 :=
  (map1BasisImage_ne_zero_iff_mem_parentRegion P A4 S q target).symm
end QEC.Coding.BDL26RZMap1CoordinateBridge
