-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalRadialParity.face_boundary_end_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:49:15.640983+00:00
-- url     : https://prove2.me/submissions/f2ed6549-a2fa-491e-83b2-6d3a903ff0b3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalRadialParity
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (face : XStarFace P x) :
    xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0) =
      xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 1) := by
  apply Subtype.ext
  rfl
end QEC.Coding.BDL26XLocalRadialParity
