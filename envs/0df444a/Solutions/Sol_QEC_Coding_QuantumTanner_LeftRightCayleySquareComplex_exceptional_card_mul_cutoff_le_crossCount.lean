-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_card_mul_cutoff_le_crossCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:44:50.021074+00:00
-- url     : https://prove2.me/submissions/028b9f3b-ab18-4c2b-ac18-a0d29e0ffbc6

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_supportSquareGraph_le_squareGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_supportSquareGraph_active_eq_localWeight
import Theorems.Thm_QEC_Coding_SmallSetExpansion_degree_mul_card_le_crossCount


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
    (x : Word (ZMod 2) Square) (cutoff : Nat) :
    cutoff * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      crossCount (X.squareGraph side) (X.exceptionalVerticesOnSide side x cutoff)
        (X.activeVerticesOnSide side x) := by
  apply degree_mul_card_le_crossCount
  intro g hg
  have hcutoff := (Finset.mem_filter.mp hg).2
  calc
    cutoff ≤ HammingWeight (X.localRestriction (g, side) x) := hcutoff
    _ = ∑ h ∈ X.activeVerticesOnSide side x, X.supportSquareGraph side x g h :=
      (X.sum_supportSquareGraph_active_eq_localWeight side x g).symm
    _ ≤ ∑ h ∈ X.activeVerticesOnSide side x, X.squareGraph side g h :=
      Finset.sum_le_sum fun h _hh => X.supportSquareGraph_le_squareGraph side x g h
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
