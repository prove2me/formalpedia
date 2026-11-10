-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le_all_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:19:57.350363+00:00
-- url     : https://prove2.me/submissions/c415f745-a9ea-42b2-9956-522f788c07de

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCx_exists_local_weight_le
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      (∑ q : P.Q, if hq : P.xq x q = true then
        HammingWeight (rxXQDegreeOne P
          A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible q x hq S f) else 0) ≤
        HammingWeight syndrome := by
  classical
  obtain ⟨f, hf, hw⟩ := rxCx_exists_local_weight_le P A4 R x S syndrome hs
  refine ⟨f, hf, ?_⟩
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let term := fun q : P.Q => if hq : P.xq x q = true then
    HammingWeight (rxXQDegreeOne P A q x hq S f) else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun q : P.Q => P.xq x q = true) term
  have hpos : (∑ q : {q : P.Q // P.xq x q = true}, term q.val) =
      connectingWeight P A x S f := by
    apply Finset.sum_congr rfl
    intro q _
    exact dif_pos q.property
  have hneg : (∑ q : {q : P.Q // ¬ P.xq x q = true}, term q.val) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact dif_neg q.property
  have hsum : (∑ q : P.Q, term q) = connectingWeight P A x S f := by
    calc
      _ = (∑ q : {q : P.Q // P.xq x q = true}, term q.val) +
          (∑ q : {q : P.Q // ¬ P.xq x q = true}, term q.val) := hsplit.symm
      _ = _ := by rw [hpos, hneg, add_zero]
  change (∑ q : P.Q, term q) ≤ HammingWeight syndrome
  rw [hsum]
  exact hw
end QEC.Coding.BDL26RXLocalReplacement
