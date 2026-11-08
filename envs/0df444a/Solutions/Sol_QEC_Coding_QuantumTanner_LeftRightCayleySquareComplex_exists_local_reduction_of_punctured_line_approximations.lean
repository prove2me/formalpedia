-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_reduction_of_punctured_line_approximations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:58.017205+00:00
-- url     : https://prove2.me/submissions/8d3efc55-37f6-488a-aa60-4b348e88e887

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_punctured_row_column_approximations
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensor_weight_reduction_of_punctured_approximation


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B)
    (dA dB w rowError columnError : Nat)
    (hA : MinimumDistance (puncturedCode CA removedA) dA)
    (hB : MinimumDistance (puncturedCode CB removedB) dB)
    (hRobust : IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w)
    (hBudget : 2 * w ≤ dA * dB)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧
      HammingWeight (rowRestriction a.1 (X.localRestriction (g, side) x) + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧
      HammingWeight (columnRestriction b.1 (X.localRestriction (g, side) x) + c) ≤ columnError)
    (hErrors : Fintype.card B * columnError + Fintype.card A * rowError ≤ w)
    (hMargin : 3 * (Fintype.card B * columnError + Fintype.card A * rowError) +
      2 * (removedA.card * Fintype.card B + Fintype.card A * removedB.card) <
      2 * HammingWeight (X.localRestriction (g, side) x)) :
    ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, side) x + c) <
        HammingWeight (X.localRestriction (g, side) x) := by
  obtain ⟨C, R, hC, hR, hCError, hRError⟩ :=
    exists_punctured_row_column_approximations CA CB removedA removedB
      (X.localRestriction (g, side) x) rowError columnError hRows hColumns
  apply exists_tensor_weight_reduction_of_punctured_approximation CA CB
    removedA removedB dA dB w hA hB hRobust hBudget
    (X.localRestriction (g, side) x) C R hC hR
  · omega
  · omega
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
