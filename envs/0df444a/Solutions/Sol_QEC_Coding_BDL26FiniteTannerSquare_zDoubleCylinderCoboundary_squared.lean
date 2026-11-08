-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderCoboundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:32.247729+00:00
-- url     : https://prove2.me/submissions/71e0b7c6-4958-4ade-a325-fac7a3b6d4d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderCoboundary_squared

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
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (doubleCylinderCoboundary1 (transposePresentation P) z S).comp
      (doubleCylinderCoboundary0 (transposePresentation P) z S) = 0 :=
  doubleCylinderCoboundary_squared (transposePresentation P) z S
end QEC.Coding.BDL26FiniteTannerSquare
