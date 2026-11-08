-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalReplacement.rzCqH1Coordinate_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:45:09.86429+00:00
-- url     : https://prove2.me/submissions/39c8956f-b2e8-4057-b654-8a22212a1998

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_graphCokernelParity_bijective

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
namespace QEC.Coding.BDL26RZLocalReplacement
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (S : OddScale) :
    Function.Bijective (rzCqH1Coordinate P q S) :=
  graphCokernelParity_bijective
    (qDoubleCylinderEdgeStart (transposePresentation P) q S)
    (qDoubleCylinderEdgeEnd (transposePresentation P) q S)
    (0, Sum.inl (Sum.inl ()))
    (qDoubleCylinderPath (transposePresentation P)
      (transposeTannerSquareAdmissible P A) q S)
end QEC.Coding.BDL26RZLocalReplacement
