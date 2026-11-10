-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.map1_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:54:12.594637+00:00
-- url     : https://prove2.me/submissions/1590ff07-c54f-4705-a546-67bc9a7b8d90

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
    Function.Injective (rxMap1Coord P S) := by
  intro u v h
  funext q
  exact congrFun h (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩)
end QEC.Coding.BDL26RXCohomology
