-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.TannerSquareCellularRegular.faceOver_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:21:27.144582+00:00
-- url     : https://prove2.me/submissions/0d2d1f12-508f-4004-9fd8-2743c5ce6663

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
namespace TannerSquareCellularRegular
theorem _root_.solution
    {P : TannerSquarePresentation} (R : TannerSquareCellularRegular P)
    (x : P.X) (z : P.Z) : Subsingleton (FaceOver P.data x z) where
  allEq := by
    intro first second
    apply Subtype.ext
    apply R.faceXZ_injective
    apply Prod.ext
    · exact first.2.1.trans second.2.1.symm
    · exact first.2.2.trans second.2.2.symm
end TannerSquareCellularRegular
end QEC.Coding.BDL26FiniteTannerSquare
