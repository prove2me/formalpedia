-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.doubleCylinderCoboundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:29:33.051565+00:00
-- url     : https://prove2.me/submissions/69456c98-91fe-498c-8a84-61f81cd42fd3

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
theorem _root_.solution
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (doubleCylinderCoboundary1 P x S).comp
      (doubleCylinderCoboundary0 P x S) = 0 := by
  rw [doubleCylinderCoboundary1, doubleCylinderCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [doubleCylinderBoundary_squared]
  exact wordLinearMapTranspose_zero
end QEC.Coding.BDL26FiniteTannerSquare
