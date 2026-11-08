-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.xBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:41.514656+00:00
-- url     : https://prove2.me/submissions/63497fb7-f503-47a0-adfd-f5dfbbb4f78d

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
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    LinearMap.range (graphBoundary (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (xBoundaryEdgeStart P x) (xBoundaryEdgeEnd P x)
    (A.xBoundaryRoot x) (A.xBoundaryPath x)
end QEC.Coding.BDL26TannerLocalRegularity
