-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.differential1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:17:46.925325+00:00
-- url     : https://prove2.me/submissions/92e945d8-e778-4953-b803-9358d63dbf90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) = rxCoboundary1 P S := by
  exact rxPresentation_coboundary1_eq P A R S
end QEC.Coding.BDL26RXCohomology
