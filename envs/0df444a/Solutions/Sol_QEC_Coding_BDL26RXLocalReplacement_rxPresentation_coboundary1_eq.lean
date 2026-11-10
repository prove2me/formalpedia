-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:19:51.848703+00:00
-- url     : https://prove2.me/submissions/7883c795-1c5d-40c0-8023-fd8772708fea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2Matrix_eq
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
private theorem rxGeneric_coboundary1_eq (P : TannerSquarePresentation) :
    tannerCoboundary1 P = wordLinearMapTranspose
      (Matrix.toLin' (fun x : P.Q => fun q : P.Z =>
        if P.qz x q = true then (1 : Field) else 0)) := by
  classical
  apply LinearMap.ext
  intro f
  apply funext
  intro q
  exact (wordLinearMapTranspose_toLin'_apply
    (fun x q => if P.qz x q = true then (1 : Field) else 0) f q).symm
end QEC.Coding.BDL26RXLocalReplacement
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (_R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary2 P S) := by
  classical
  have hm : (fun x : RX1 P S => fun q : RX2 P S =>
      if (rxReplacementPresentation P S).qz x q = true then (1 : Field) else 0) =
      rxBoundary2Matrix P S := by
    funext x q
    exact (rxPresentation_boundary2Matrix_eq P A4 S x q).symm
  exact (rxGeneric_coboundary1_eq (rxReplacementPresentation P S)).trans
    (congrArg (fun M : Matrix (RX1 P S) (RX2 P S) Field =>
      wordLinearMapTranspose (Matrix.toLin' M)) hm)
end QEC.Coding.BDL26RXLocalReplacement
