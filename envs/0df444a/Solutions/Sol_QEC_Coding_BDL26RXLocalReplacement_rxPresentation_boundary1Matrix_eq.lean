-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1Matrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:16:52.273978+00:00
-- url     : https://prove2.me/submissions/adb81c54-6a8f-4ad5-b46e-c2b4d3ad1d5f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1_local_eq_one_iff
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1_qVertex_eq_one_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : RX0 P S) (q : RX1 P S) :
    rxBoundary1Matrix P S x q =
      if (rxReplacementPresentation P S).xq x q = true then 1 else 0 := by
  classical
  have hiff : rxBoundary1Matrix P S x q = 1 ↔
      (rxReplacementPresentation P S).xq x q = true := by
    rcases q with edge | vertex
    · exact rxPresentation_boundary1_local_eq_one_iff
        P A4.toTannerSquareAdmissibleV3 S x edge
    · exact rxPresentation_boundary1_qVertex_eq_one_iff
        P A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S x vertex
  generalize hv : rxBoundary1Matrix P S x q = value at *
  fin_cases value
  · have hn := fun hp => zero_ne_one (hiff.mpr hp)
    rw [if_neg hn]
    rfl
  · have hp := hiff.mp rfl
    rw [if_pos hp]
    rfl
end QEC.Coding.BDL26RXLocalReplacement
