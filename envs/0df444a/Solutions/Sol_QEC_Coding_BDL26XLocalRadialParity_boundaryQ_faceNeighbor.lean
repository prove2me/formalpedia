-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalRadialParity.boundaryQ_faceNeighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:49:12.92874+00:00
-- url     : https://prove2.me/submissions/de08ec5a-e57f-43f3-9b65-620fb4140e7d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalRadialParity
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (face : XStarFace P x) (side : Two) :
    boundaryQ P A x (faceNeighbor P x face side) =
      xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side) := by
  apply Subtype.ext
  rfl
end QEC.Coding.BDL26XLocalRadialParity
