-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.supportSquareGraph_le_squareGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:21.694254+00:00
-- url     : https://prove2.me/submissions/8be4a0db-c1a3-42ae-9227-1ff6be730cb7

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g h : G) :
    X.supportSquareGraph side x g h ≤ X.squareGraph side g h := by
  apply Finset.card_le_card
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2.2⟩
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
