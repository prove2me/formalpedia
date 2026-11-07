-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnWeight_le_unionDegree_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:07:54.620985+00:00
-- url     : https://prove2.me/submissions/392a3795-0446-4056-a26d-9e3a62db8946

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_unionCayleyGraph_eq_labels
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_left_neighbor_mem_active_of_entry_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    HammingWeight (columnRestriction b (X.localRestriction (g, side) x)) ≤
      ∑ h ∈ X.activeVerticesOnSide (!side) x, X.unionCayleyGraph g h := by
  rw [X.sum_unionCayleyGraph_eq_labels]
  have hSubset : hammingSupport (columnRestriction b (X.localRestriction (g, side) x)) ⊆
      Finset.univ.filter (fun a => X.leftGenerator a * g ∈
        X.activeVerticesOnSide (!side) x) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      X.left_neighbor_mem_active_of_entry_ne_zero hX x g side a b
        (Finset.mem_filter.mp ha).2⟩
  exact (Finset.card_le_card hSubset).trans (Nat.le_add_right _ _)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
