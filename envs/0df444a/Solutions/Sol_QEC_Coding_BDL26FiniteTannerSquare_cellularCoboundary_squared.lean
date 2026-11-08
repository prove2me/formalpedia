-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.cellularCoboundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:38:52.7085+00:00
-- url     : https://prove2.me/submissions/bd213ced-a208-4873-a123-65cab601f0fd

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
theorem _root_.solution (P : TannerSquarePresentation) :
    (cellularCoboundary1 P).comp (cellularCoboundary0 P) = 0 := by
  rw [cellularCoboundary1, cellularCoboundary0]
  rw [← wordLinearMapTranspose_comp]
  rw [cellularBoundary_squared]
  exact wordLinearMapTranspose_zero
end QEC.Coding.BDL26FiniteTannerSquare
