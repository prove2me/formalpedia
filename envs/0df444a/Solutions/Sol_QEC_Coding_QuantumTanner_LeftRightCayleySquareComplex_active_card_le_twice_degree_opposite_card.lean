-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.active_card_le_twice_degree_opposite_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:11:24.357679+00:00
-- url     : https://prove2.me/submissions/c2569520-cc40-42a0-a324-da82505a0de5

import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_DegreeSelection
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_crossCount_unionCayleyGraph_le_degree_card_right
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_heavyUnionGraph_le_unionCayleyGraph


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat)
    (S exceptional : Finset G) (hExceptional : 2 * (S ∩ exceptional).card ≤ S.card)
    (hCoverage : (S \ exceptional).card ≤
      crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional))) :
    S.card ≤ 2 * (Fintype.card A + Fintype.card B) *
      (X.oppositeHeavySet side x cutoff (S \ exceptional)).card := by
  have hCross : crossCount (X.heavyUnionGraph side x cutoff) (S \ exceptional)
      (X.oppositeHeavySet side x cutoff (S \ exceptional)) ≤
      crossCount X.unionCayleyGraph (S \ exceptional)
        (X.oppositeHeavySet side x cutoff (S \ exceptional)) := by
    apply Finset.sum_le_sum
    intro g hg
    apply Finset.sum_le_sum
    intro h hh
    exact X.heavyUnionGraph_le_unionCayleyGraph side x cutoff g h
  have hDegree := X.crossCount_unionCayleyGraph_le_degree_card_right
    (S \ exceptional) (X.oppositeHeavySet side x cutoff (S \ exceptional))
  have hPartition := Finset.card_sdiff_add_card_inter S exceptional
  nlinarith
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
