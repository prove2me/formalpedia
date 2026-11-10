-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.map2_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:19:48.980249+00:00
-- url     : https://prove2.me/submissions/88a7d9ff-6917-41f3-99cf-231a994551d3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (rxMap2Coord P S) := by
  intro u v h
  funext z
  exact congrFun h (Sum.inr (z,0))
end QEC.Coding.BDL26RXCohomology
