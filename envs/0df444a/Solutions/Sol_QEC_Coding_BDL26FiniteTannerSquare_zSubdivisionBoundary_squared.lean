-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.zSubdivisionBoundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:19.358678+00:00
-- url     : https://prove2.me/submissions/33a2b41b-edb9-425d-a57a-24ee92fd9efd

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
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :
    (subdivisionBoundary1 (transposePresentation P) z S).comp
      (subdivisionBoundary2 (transposePresentation P) z S) = 0 :=
  subdivisionBoundary_squared (transposePresentation P) z S
end QEC.Coding.BDL26FiniteTannerSquare
