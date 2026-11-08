-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionCoboundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:28.40052+00:00
-- url     : https://prove2.me/submissions/0a846f45-f02c-4bcf-8078-6d40c7c2fa6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_subdivisionCoboundary_squared

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
    (subdivisionCoboundary1 (transposePresentation P) z S).comp
      (subdivisionCoboundary0 (transposePresentation P) z S) = 0 :=
  subdivisionCoboundary_squared (transposePresentation P) z S
end QEC.Coding.BDL26FiniteTannerSquare
