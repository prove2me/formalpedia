-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.qSubdivisionBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:42:18.421619+00:00
-- url     : https://prove2.me/submissions/32b77a22-d947-4bdc-abf1-55c57178e0c0

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
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) :
    LinearMap.range (qSubdivisionBoundary1 P q S) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qSubdivisionEdgeStart P q S) (qSubdivisionEdgeEnd P q S)
    (Sum.inl (Sum.inl ())) (qSubdivisionPath P q S)
end QEC.Coding.BDL26TannerLocalRegularity
