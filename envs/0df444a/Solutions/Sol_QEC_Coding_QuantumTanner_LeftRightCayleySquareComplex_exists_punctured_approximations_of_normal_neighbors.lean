-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_punctured_approximations_of_normal_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:11:58.044232+00:00
-- url     : https://prove2.me/submissions/04d08120-a7c9-42f4-bad7-47a8ed9cc8c5

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_columnRestriction_localRestriction_rebase_right
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rowRestriction_localRestriction_rebase_left
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_punctured_row_column_approximations
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_row_column_approximations_of_cover


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat) (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool)
    (removedA : Finset A) (removedB : Finset B) (rowError columnError : Nat)
    (hLeft : ∀ a : KeptCoordinate removedA, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (X.leftGenerator a.1 * g, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (X.leftGenerator a.1 * g, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ columns.card ≤ rowError)
    (hRight : ∀ b : KeptCoordinate removedB, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g * X.rightGenerator b.1, !side) x ∈
        (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g * X.rightGenerator b.1, !side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧ rows.card ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB (X.localRestriction (g, side) x) + R) ≤
        Fintype.card A * rowError := by
  apply exists_punctured_row_column_approximations CA CB removedA removedB
    (X.localRestriction (g, side) x) rowError columnError
  · intro a
    obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hError⟩ := hLeft a
    obtain ⟨r, c, hr, hc, hParts, hRowError, hColumnError, hHeavyRow, hHeavyColumn⟩ :=
      exists_row_column_approximations_of_cover CA CB dA dB hA hB
        (X.localRestriction (X.leftGenerator a.1 * g, !side) x) hLocal
        rows columns hRows hColumns hCovered
    refine ⟨rowRestriction (X.leftInverse a.1) r, hr _, ?_⟩
    rw [X.rowRestriction_localRestriction_rebase_left hX]
    exact (hRowError _).trans hError
  · intro b
    obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hError⟩ := hRight b
    obtain ⟨r, c, hr, hc, hParts, hRowError, hColumnError, hHeavyRow, hHeavyColumn⟩ :=
      exists_row_column_approximations_of_cover CA CB dA dB hA hB
        (X.localRestriction (g * X.rightGenerator b.1, !side) x) hLocal
        rows columns hRows hColumns hCovered
    refine ⟨columnRestriction (X.rightInverse b.1) c, hc _, ?_⟩
    rw [X.columnRestriction_localRestriction_rebase_right hX]
    exact (hColumnError _).trans hError
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
