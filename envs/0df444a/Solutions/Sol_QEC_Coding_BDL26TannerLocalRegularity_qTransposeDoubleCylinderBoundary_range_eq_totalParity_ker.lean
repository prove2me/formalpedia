-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.qTransposeDoubleCylinderBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:42:56.375988+00:00
-- url     : https://prove2.me/submissions/2ada2df4-70c6-4cf8-b5c1-34549b62b0db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qDoubleCylinderBoundary_range_eq_totalParity_ker

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u
namespace QEC.Coding.BDL26TannerLocalRegularity
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (S : OddScale) :
    LinearMap.range
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      LinearMap.ker totalParity :=
  qDoubleCylinderBoundary_range_eq_totalParity_ker
    (transposePresentation P) (transposeTannerSquareAdmissible P A) q S
end QEC.Coding.BDL26TannerLocalRegularity
