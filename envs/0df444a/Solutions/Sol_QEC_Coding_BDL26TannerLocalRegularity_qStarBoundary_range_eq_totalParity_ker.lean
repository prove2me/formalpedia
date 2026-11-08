-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.qStarBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:42:16.489844+00:00
-- url     : https://prove2.me/submissions/5a0d2867-dda3-4b7e-a72c-4e9f10919983

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
    (P : TannerSquarePresentation) (q : P.Q) :
    LinearMap.range (qStarBoundary1 P q) = LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (qStarEdgeStart P q) (qStarEdgeEnd P q) (Sum.inl ()) (qStarPath P q)
end QEC.Coding.BDL26TannerLocalRegularity
