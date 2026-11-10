-- Prove2me | solution 1 for QEC.Coding.BDL26RZCohomology.equiv_symm_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:38:42.785753+00:00
-- url     : https://prove2.me/submissions/ccdd4d7f-6edd-4654-aa82-c85feeae011b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_backward_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RZCohomology.backward_mk



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance BDL26RZLocalReplacement
namespace QEC.Coding.BDL26RZCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : Cocycle (successor P A4 S)) :
    (equiv P A4 R S).symm (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := backward_mk P A4 S w
end QEC.Coding.BDL26RZCohomology
