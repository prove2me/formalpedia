-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.doubleCylinder_rectangle_vertical_start_from_construction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:40:51.621936+00:00
-- url     : https://prove2.me/submissions/df096487-ed1c-4eb4-9e78-139fb6a6fe63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionBoundaryEdgeStart_ne_end
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinder_rectangle_vertical_start

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq
namespace QEC.Coding.BDL26FiniteTannerSquare
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S
      (Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle))
      (Sum.inr rectangle) = 1 :=
  doubleCylinder_rectangle_vertical_start P x S rectangle
    (subdivisionBoundaryEdgeStart_ne_end P x S rectangle)
end QEC.Coding.BDL26FiniteTannerSquare
