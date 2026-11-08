-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.base_xqIncidenceMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:38:54.51121+00:00
-- url     : https://prove2.me/submissions/df82bb5b-df90-4aa8-b9d9-abf0dba2477c

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
theorem _root_.solution :
    xqIncidenceMatrix baseTannerSquarePresentation = baseBoundary1Matrix := by
  change (fun (x : BaseX) (q : BaseQubit) =>
    if decide (baseBoundary1Matrix x q ≠ 0) then (1 : Field) else 0) = _
  funext x q
  fin_cases x <;> fin_cases q <;> decide
end QEC.Coding.BDL26FiniteTannerSquare
