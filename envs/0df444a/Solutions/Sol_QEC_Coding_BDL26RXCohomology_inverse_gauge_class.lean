-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.inverse_gauge_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:16:49.546049+00:00
-- url     : https://prove2.me/submissions/02a14017-ee39-44fc-aa47-faf82b1dffbe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (v : Cocycle P)
    (f : Word Field (RX0 P S))
    (hf : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f) :
    (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by
  apply (equiv P A R S).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (gauge_class P A R S w v f hf).symm
end QEC.Coding.BDL26RXCohomology
