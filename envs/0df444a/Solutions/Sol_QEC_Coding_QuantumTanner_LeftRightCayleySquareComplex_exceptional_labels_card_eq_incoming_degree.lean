-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_labels_card_eq_incoming_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:12:34.45961+00:00
-- url     : https://prove2.me/submissions/4f491f0a-b4df-4a49-931d-55e2d7d43ee0

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_unionCayleyGraph_eq_labels
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (exceptional : Finset G) :
    (X.exceptionalLeftLabels g exceptional).card +
      (X.exceptionalRightLabels g exceptional).card =
      ∑ h ∈ exceptional, X.unionCayleyGraph h g := by
  unfold exceptionalLeftLabels exceptionalRightLabels
  rw [← X.sum_unionCayleyGraph_eq_labels]
  apply Finset.sum_congr rfl
  intro h hh
  exact X.unionCayleyGraph_symmetric g h
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
