-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.zDoubleCylinderBoundary_squared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:30.369765+00:00
-- url     : https://prove2.me/submissions/3f02d998-a24e-4a31-87f8-023a49099371

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
    (doubleCylinderBoundary1 (transposePresentation P) z S).comp
      (doubleCylinderBoundary2 (transposePresentation P) z S) = 0 :=
  doubleCylinderBoundary_squared (transposePresentation P) z S
end QEC.Coding.BDL26FiniteTannerSquare
