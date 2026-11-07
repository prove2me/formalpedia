-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_balanced_nonexceptional_neighbor_punctures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:17:19.679518+00:00
-- url     : https://prove2.me/submissions/fc17f37c-fec6-4dfd-b4a4-962d7cfefcd5

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_labels_card_eq_incoming_degree
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_balanced_punctures


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G)
    (p : Nat) (hCard : Fintype.card A = Fintype.card B) (hp : p ≤ Fintype.card A)
    (hBad : (∑ h ∈ exceptional, X.unionCayleyGraph h g) ≤ p) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      removedA.card = removedB.card ∧ removedA.card ≤ p ∧
      (∀ a : KeptCoordinate removedA, X.leftGenerator a.1 * g ∉ exceptional) ∧
      (∀ b : KeptCoordinate removedB, g * X.rightGenerator b.1 ∉ exceptional) := by
  have hCount := X.exceptional_labels_card_eq_incoming_degree g exceptional
  have hLeft : (X.exceptionalLeftLabels g exceptional).card ≤ p := by omega
  have hRight : (X.exceptionalRightLabels g exceptional).card ≤ p := by omega
  obtain ⟨removedA, removedB, hContainsA, hContainsB, hEqual, hSize⟩ :=
    exists_balanced_punctures (X.exceptionalLeftLabels g exceptional)
      (X.exceptionalRightLabels g exceptional) p hCard hLeft hRight hp
  refine ⟨removedA, removedB, hEqual, hSize, ?_, ?_⟩
  · intro a ha
    exact a.2 (hContainsA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
  · intro b hb
    exact b.2 (hContainsB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩))
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
