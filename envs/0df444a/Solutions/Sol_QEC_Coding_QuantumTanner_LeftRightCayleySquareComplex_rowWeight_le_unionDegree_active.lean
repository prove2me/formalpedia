-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rowWeight_le_unionDegree_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:09:23.856837+00:00
-- url     : https://prove2.me/submissions/d534635d-f7c6-4ba5-a0fb-46d7ec2119a3

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_unionCayleyGraph_eq_labels
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_right_neighbor_mem_active_of_entry_ne_zero

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
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) :
    HammingWeight (rowRestriction a (X.localRestriction (g, side) x)) ≤
      ∑ h ∈ X.activeVerticesOnSide (!side) x, X.unionCayleyGraph g h := by
  rw [X.sum_unionCayleyGraph_eq_labels]
  have hSubset : hammingSupport (rowRestriction a (X.localRestriction (g, side) x)) ⊆
      Finset.univ.filter (fun b => g * X.rightGenerator b ∈
        X.activeVerticesOnSide (!side) x) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      X.right_neighbor_mem_active_of_entry_ne_zero hX x g side a b
        (Finset.mem_filter.mp hb).2⟩
  exact (Finset.card_le_card hSubset).trans (Nat.le_add_left _ _)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
