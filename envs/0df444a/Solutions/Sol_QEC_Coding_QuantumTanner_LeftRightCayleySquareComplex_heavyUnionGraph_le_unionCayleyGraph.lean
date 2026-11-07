-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.heavyUnionGraph_le_unionCayleyGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:51:28.566498+00:00
-- url     : https://prove2.me/submissions/9b0fba57-15b4-4fd5-ba99-40562f7dc581

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (g h : G) :
    X.heavyUnionGraph side x cutoff g h ≤ X.unionCayleyGraph g h := by
  apply Nat.add_le_add
  · apply Finset.card_le_card
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
  · apply Finset.card_le_card
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
