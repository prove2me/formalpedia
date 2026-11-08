-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzQZH1ToH2_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:10:15.239029+00:00
-- url     : https://prove2.me/submissions/217db0ed-2c6a-4cd1-a060-160e9bb9e075

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzQZDegreeOne_totalParity

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (cohomologyClass : RZQH1 P q S) :
    rzCzH2Coordinate P z S
        (rzQZH1ToH2 P A q z hqz S cohomologyClass) =
      rzCqH1Coordinate P q S cohomologyClass := by
  refine Submodule.Quotient.induction_on _ cohomologyClass ?_
  intro word
  change rzCzH2Coordinate P z S
      (rzQZH1ToH2 P A q z hqz S
        ((LinearMap.range
          (qDoubleCylinderBoundary1
            (transposePresentation P) q S)).mkQ word)) =
    rzCqH1Coordinate P q S
      ((LinearMap.range
        (qDoubleCylinderBoundary1
          (transposePresentation P) q S)).mkQ word)
  rw [rzQZH1ToH2_mk, rzCzH2Coordinate_mk]
  change totalParity (rzQZDegreeOne P A q z hqz S word) =
    totalParity word
  exact rzQZDegreeOne_totalParity P A q z hqz S word
end QEC.Coding.BDL26RZLocalReplacement
