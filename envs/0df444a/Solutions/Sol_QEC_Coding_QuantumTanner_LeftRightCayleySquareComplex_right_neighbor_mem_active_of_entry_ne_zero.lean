-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.right_neighbor_mem_active_of_entry_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:06:59.959648+00:00
-- url     : https://prove2.me/submissions/a30601cd-d9b7-404f-85cc-9b57cd128aae

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
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) (b : B)
    (hEntry : X.localRestriction (g, side) x (a, b) ≠ 0) :
    g * X.rightGenerator b ∈ X.activeVerticesOnSide (!side) x := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hZero
  apply hEntry
  change x (X.link (g, side) (a, b)) = 0
  rw [hX.2 g side a b]
  exact congrFun hZero (a, X.rightInverse b)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
