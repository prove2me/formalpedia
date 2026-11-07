-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_incoming_heavyDegree_le_twice_localWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:12:45.361018+00:00
-- url     : https://prove2.me/submissions/23602d7f-1566-49f8-8ae7-8a6ecae7ed29

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_heavyUnionGraph_reverse
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_heavyDegree_le_twice_localWeight

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
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) (h : G) :
    cutoff * (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
      2 * HammingWeight (X.localRestriction (h, !side) x) := by
  have hDegree : (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
      ∑ g : G, X.heavyUnionGraph (!side) x cutoff h g := by
    simp_rw [X.heavyUnionGraph_reverse hX side x cutoff]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ normal)
    intro g hg hNot
    exact Nat.zero_le _
  exact (Nat.mul_le_mul_left cutoff hDegree).trans
    (X.cutoff_mul_heavyDegree_le_twice_localWeight (!side) x cutoff h)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
