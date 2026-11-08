-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.zBoundary_range_eq_totalParity_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:42:04.030341+00:00
-- url     : https://prove2.me/submissions/24114cf8-113e-428e-a698-0f746dc7c9d4

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
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (z : P.Z) :
    LinearMap.range (graphBoundary (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)) =
      LinearMap.ker totalParity :=
  graphBoundary_range_eq_totalParity_ker
    (zBoundaryEdgeStart P z) (zBoundaryEdgeEnd P z)
    (A.zBoundaryRoot z) (A.zBoundaryPath z)
end QEC.Coding.BDL26TannerLocalRegularity
