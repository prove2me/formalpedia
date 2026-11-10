-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.equiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:39:37.334038+00:00
-- url     : https://prove2.me/submissions/7955217c-5bfa-4ead-b8b1-9e042157101a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_forward_mk
attribute [local simp] QEC.Coding.BDL26RZCohomology.forward_mk



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance BDL26RZLocalReplacement
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A4 R S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := forward_mk P A4 S v
end QEC.Coding.BDL26RZCohomology
