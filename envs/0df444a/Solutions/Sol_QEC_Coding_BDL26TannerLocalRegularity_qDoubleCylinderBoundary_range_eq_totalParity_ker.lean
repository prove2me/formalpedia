-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:39:03.288288+00:00
-- url     : https://prove2.me/submissions/2ba99d0e-867e-4e48-9cc8-bb284e0056b7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_range_eq_totalParity_ker

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
    LinearMap.range (qDoubleCylinderBoundary1 P q S) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)
end QEC.Coding.BDL26TannerLocalRegularity
