-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.subdivision_original_boundary_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:39:07.154601+00:00
-- url     : https://prove2.me/submissions/100dc3c4-5cee-468f-bedf-3708460703b3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare

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
theorem _root_.solution (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (v : XStarVertex P x) :
    subdivisionBoundaryVertexMember P x S (Sum.inl v) =
      xStarBoundaryVertexMember P x v.1 := rfl
end QEC.Coding.BDL26FiniteTannerSquare
