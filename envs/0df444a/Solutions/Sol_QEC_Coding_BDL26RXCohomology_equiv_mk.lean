-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.equiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:18:09.526252+00:00
-- url     : https://prove2.me/submissions/cb1cd318-b4b5-42f7-a527-6f0b908990f5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.forward_mk



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A R S (classOf P v) =
      classOf (rxReplacementPresentation P S) (forwardCocycle P A R S v) := forward_mk P A R S v
end QEC.Coding.BDL26RXCohomology
