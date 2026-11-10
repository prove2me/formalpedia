-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:20:27.172078+00:00
-- url     : https://prove2.me/submissions/933b6d52-f920-478d-8ebd-f66a3e046294

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1Matrix_eq
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
private theorem rxGeneric_coboundary0_eq (P : TannerSquarePresentation) :
    tannerCoboundary0 P = wordLinearMapTranspose
      (Matrix.toLin' (fun x : P.X => fun q : P.Q =>
        if P.xq x q = true then (1 : Field) else 0)) := by
  classical
  apply LinearMap.ext
  intro f
  apply funext
  intro q
  exact (wordLinearMapTranspose_toLin'_apply
    (fun x q => if P.xq x q = true then (1 : Field) else 0) f q).symm
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
    tannerCoboundary0 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary1 P S) := by
  classical
  have hm : (fun x : RX0 P S => fun q : RX1 P S =>
      if (rxReplacementPresentation P S).xq x q = true then (1 : Field) else 0) =
      rxBoundary1Matrix P S := by
    funext x q
    exact (rxPresentation_boundary1Matrix_eq P A4 S x q).symm
  exact (rxGeneric_coboundary0_eq (rxReplacementPresentation P S)).trans
    (congrArg (fun M : Matrix (RX0 P S) (RX1 P S) Field =>
      wordLinearMapTranspose (Matrix.toLin' M)) hm)
end QEC.Coding.BDL26RXLocalReplacement
