-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary2Matrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:16:33.414203+00:00
-- url     : https://prove2.me/submissions/76847b4d-54ea-43ce-a8bf-ea89268ec136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2_face_corner
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2_local_mem
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2_qEdge_mem
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2_oldZ_mem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : RX1 P S) (z : RX2 P S) :
    rxBoundary2Matrix P S q z =
      if (rxReplacementPresentation P S).qz q z = true then 1 else 0 := by
  classical
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  have hiff : rxBoundary2Matrix P S q z = 1 ↔
      (rxReplacementPresentation P S).qz q z = true := by
    constructor
    · intro h
      rcases z with (cell | edge) | old
      · exact rxPresentation_boundary2_local_mem P S q cell h
      · exact rxPresentation_boundary2_qEdge_mem P A S q edge h
      · exact rxPresentation_boundary2_oldZ_mem P A S q old h
    · intro h
      obtain ⟨face, corner, hq, hz⟩ :=
        (rxQZIncidence_eq_true_iff P S _ _).1 h
      rw [← hq, ← hz]
      exact rxPresentation_boundary2_face_corner P A S face corner
  generalize hv : rxBoundary2Matrix P S q z = value at *
  fin_cases value
  · have hn := fun hp => zero_ne_one (hiff.mpr hp)
    rw [if_neg hn]
    rfl
  · have hp := hiff.mp rfl
    rw [if_pos hp]
    rfl
end QEC.Coding.BDL26RXLocalReplacement
