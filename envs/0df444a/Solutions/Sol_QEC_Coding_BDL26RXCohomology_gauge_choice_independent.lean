-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.gauge_choice_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:48:38.09396+00:00
-- url     : https://prove2.me/submissions/83c97289-7f55-48d7-9c51-382c189d17c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_inverse_gauge_class
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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
    (w : Cocycle (rxReplacementPresentation P S)) (u v : Cocycle P)
    (f g : Word Field (RX0 P S))
    (hf : rxMap1Coord P S u.1 = coordinateWord P S w.1 - rxCoboundary0 P S f)
    (hg : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S g) :
    u.1 - v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier := by
  have hclasses : classOf P u = classOf P v :=
    (inverse_gauge_class P A R S w u f hf).symm.trans (inverse_gauge_class P A R S w v g hg)
  have hz : classOf P (u-v) = 0 := by rw [map_sub, hclasses, sub_self]
  have hb := (Submodule.Quotient.mk_eq_zero
    (complex P).middleCoboundaryInCocycles).mp hz
  change u.1 - v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier at hb
  exact hb
end QEC.Coding.BDL26RXCohomology
