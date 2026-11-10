-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCq_exists_local_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:55:35.231769+00:00
-- url     : https://prove2.me/submissions/418650b2-56ce-4c8c-84f4-528a0cd67910

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocalCoboundary_add_constant
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_terminal_weight_le_of_centers_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_card_le_weight_of_centers_ne
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_terminal_weight_complement
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ f : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f = syndrome ∧
        (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) ≤
          HammingWeight syndrome := by
  classical
  obtain ⟨h, rfl⟩ := hs
  by_cases hc : h (0, Sum.inl (Sum.inl ())) = h (1, Sum.inl (Sum.inl ()))
  · let f : Word Field (QDoubleCylinderVertex P q S) :=
      fun v => h v + h (0, Sum.inl (Sum.inl ()))
    have hf : wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f =
        wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) h :=
      qLocalCoboundary_add_constant P q S h _
    refine ⟨f, hf, ?_⟩
    rw [← hf]
    apply qLocal_terminal_weight_le_of_centers_zero P q S f
    · exact ZModModule.add_self _
    · change h (1, Sum.inl (Sum.inl ())) + h (0, Sum.inl (Sum.inl ())) = 0
      rw [← hc]
      exact ZModModule.add_self _
  · have hcard := qLocal_card_le_weight_of_centers_ne P q S h hc
    have hcomp := qLocal_terminal_weight_complement P q S h
    by_cases hsmall : (∑ z : QStarEdge P q,
        HammingWeight (rxQZDegreeOne P q z.val z.property S h)) ≤
          Fintype.card (QStarEdge P q)
    · exact ⟨h, rfl, hsmall.trans hcard⟩
    · refine ⟨fun v => h v + 1, qLocalCoboundary_add_constant P q S h 1, ?_⟩
      omega
end QEC.Coding.BDL26RXLocalReplacement
