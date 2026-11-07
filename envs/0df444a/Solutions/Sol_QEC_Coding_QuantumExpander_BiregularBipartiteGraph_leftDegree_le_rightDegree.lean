-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leftDegree_le_rightDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:43:56.498202+00:00
-- url     : https://prove2.me/submissions/b47439df-15a5-4b93-8b91-8ebe6bac5452

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_card_mul_leftDegree_eq_card_mul_rightDegree

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace QEC.Coding.QuantumExpander.BiregularBipartiteGraph
theorem _root_.solution
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    G.leftDegree ≤ G.rightDegree := by
  by_contra hDegree
  have hRightCard : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr G.rightNonempty
  have hStrict :
      Fintype.card B * G.rightDegree <
        Fintype.card B * G.leftDegree :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hDegree) hRightCard
  have hWeak :
      Fintype.card B * G.leftDegree ≤
        Fintype.card A * G.leftDegree :=
    Nat.mul_le_mul_right G.leftDegree hSize
  have hBalance := card_mul_leftDegree_eq_card_mul_rightDegree G
  omega
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
