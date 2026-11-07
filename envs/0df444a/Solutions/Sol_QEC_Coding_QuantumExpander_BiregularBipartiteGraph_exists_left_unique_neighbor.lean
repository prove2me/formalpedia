-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.exists_left_unique_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:42:50.924372+00:00
-- url     : https://prove2.me/submissions/9eed4dc7-7ba4-44d6-aac3-3c2a47f612f5

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_sum_leftInducedDegree
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_two_mul_leftNeighborhood_card_le_sum_of_no_unique

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
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2)
    (S : Finset A) (hS : S.Nonempty)
    (hSmall : (S.card : Real) ≤ γ * Fintype.card A) :
    ∃ b, G.leftInducedDegree S b = 1 := by
  by_contra hUnique
  have hNoUnique : ∀ b, G.leftInducedDegree S b ≠ 1 := by
    intro b hb
    exact hUnique ⟨b, hb⟩
  have hCountNat :
      2 * (G.leftNeighborhood S).card ≤ S.card * G.leftDegree := by
    rw [← sum_leftInducedDegree G S]
    exact two_mul_leftNeighborhood_card_le_sum_of_no_unique G S hNoUnique
  have hCountReal :
      (2 : Real) * (G.leftNeighborhood S).card ≤
        S.card * G.leftDegree := by
    exact_mod_cast hCountNat
  have hExpansion := hExpand S hSmall
  have hPositive : (0 : Real) < G.leftDegree * S.card := by
    exact mul_pos (by exact_mod_cast G.leftDegree_pos)
      (by exact_mod_cast Finset.card_pos.mpr hS)
  have hStrict :
      (1 / 2 : Real) * (G.leftDegree * S.card) <
        (1 - δ) * (G.leftDegree * S.card) := by
    apply mul_lt_mul_of_pos_right _ hPositive
    linarith
  norm_num at hStrict
  nlinarith
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
