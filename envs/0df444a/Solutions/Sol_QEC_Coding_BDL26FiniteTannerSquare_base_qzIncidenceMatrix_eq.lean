-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteTannerSquare.base_qzIncidenceMatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:38:56.364306+00:00
-- url     : https://prove2.me/submissions/78a82534-7f11-41d9-8ad5-df1877bfc060

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
    qzIncidenceMatrix baseTannerSquarePresentation = baseBoundary2Matrix := by
  change (fun (q : BaseQubit) (z : BaseZ) =>
    if decide (baseBoundary2Matrix q z ≠ 0) then (1 : Field) else 0) = _
  funext q z
  fin_cases q <;> fin_cases z <;> decide
end QEC.Coding.BDL26FiniteTannerSquare
