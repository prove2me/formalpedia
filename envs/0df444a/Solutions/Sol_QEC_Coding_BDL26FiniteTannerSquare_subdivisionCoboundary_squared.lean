-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.subdivisionCoboundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:28:41.776071+00:00
-- url     : https://prove2.me/submissions/8365f552-1bef-4cf8-a012-1283edae1a22

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
    (S : OddScale) :
    (subdivisionCoboundary1 P x S).comp (subdivisionCoboundary0 P x S) = 0 := by
  rw [subdivisionCoboundary1, subdivisionCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [subdivisionBoundary_squared]
  exact wordLinearMapTranspose_zero
end QEC.Coding.BDL26FiniteTannerSquare
