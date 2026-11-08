-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation.faceQ_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:20:07.017205+00:00
-- url     : https://prove2.me/submissions/597561d9-9101-4f64-8fae-88d1af348431

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
open QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation
namespace QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation
theorem _root_.solution (P : TannerSquarePresentation) (f : P.Face) :
    Function.Injective (P.faceQ f) := by
  intro first second hq
  let firstCorner : FaceOver P.data (P.faceX f) (P.faceZ f) × Two :=
    (⟨f, rfl, rfl⟩, first)
  let secondCorner : FaceOver P.data (P.faceX f) (P.faceZ f) × Two :=
    (⟨f, rfl, rfl⟩, second)
  have hshared :
      faceCornerToShared P.data (P.faceX f) (P.faceZ f) firstCorner =
        faceCornerToShared P.data (P.faceX f) (P.faceZ f) secondCorner := by
    apply Subtype.ext
    exact hq
  have hcorner := (P.perfectPairing (P.faceX f) (P.faceZ f)).1 hshared
  exact congrArg Prod.snd hcorner
end QEC.Coding.BDL26FiniteTannerSquare.TannerSquarePresentation
