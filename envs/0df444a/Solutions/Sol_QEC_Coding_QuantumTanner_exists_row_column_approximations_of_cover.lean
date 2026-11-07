-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_row_column_approximations_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:07:59.658756+00:00
-- url     : https://prove2.me/submissions/f76cb56c-9766-43b7-aaa3-d17a4bacb862

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Theorems.Thm_QEC_Coding_QuantumTanner_rowWeight_le_of_column_support
import Theorems.Thm_QEC_Coding_QuantumTanner_columnWeight_le_of_row_support
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_supported_decomposition_of_cover


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA)
    (hB : HasMinimumDistanceAtLeast CB dB)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier)
    (rows : Finset A) (columns : Finset B)
    (hRows : rows.card < dA) (hColumns : columns.card < dB)
    (hCovered : SupportCovered x rows columns) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧ x = r + c ∧
      (∀ a, HammingWeight (rowRestriction a x + rowRestriction a r) ≤ columns.card) ∧
      (∀ b, HammingWeight (columnRestriction b x + columnRestriction b c) ≤ rows.card) ∧
      (∀ a, rowRestriction a r ≠ 0 →
        dB ≤ HammingWeight (rowRestriction a x) + columns.card) ∧
      (∀ b, columnRestriction b c ≠ 0 →
        dA ≤ HammingWeight (columnRestriction b x) + rows.card) := by
  obtain ⟨r, c, hr, hc, hParts, hRowSupport, hColumnSupport⟩ :=
    exists_supported_decomposition_of_cover CA CB dA dB hA hB
      x hx rows columns hRows hColumns hCovered
  have hCancel {ι : Type v} (p q : Word (ZMod 2) ι) : (p + q) + p = q := by
    have hSelf : p + p = 0 := by
      ext i
      exact CharTwo.add_self_eq_zero _
    calc
      (p + q) + p = (p + p) + q := by abel
      _ = q := by rw [hSelf, zero_add]
  have hRowError (a : A) : rowRestriction a x + rowRestriction a r =
      rowRestriction a c := by
    rw [hParts, map_add]
    exact hCancel _ _
  have hColumnError (b : B) : columnRestriction b x + columnRestriction b c =
      columnRestriction b r := by
    rw [hParts, map_add, add_comm (columnRestriction b r) (columnRestriction b c)]
    exact hCancel _ _
  refine ⟨r, c, hr, hc, hParts, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hRowError]
    exact rowWeight_le_of_column_support c columns hColumnSupport a
  · intro b
    rw [hColumnError]
    exact columnWeight_le_of_row_support r rows hRowSupport b
  · intro a ha
    have hDistance := hB _ (hr a) ha
    have hTriangle := HammingWeight_add_le (rowRestriction a x) (rowRestriction a c)
    have hSame : rowRestriction a x + rowRestriction a c = rowRestriction a r := by
      rw [hParts, map_add, add_comm (rowRestriction a r) (rowRestriction a c)]
      exact hCancel _ _
    rw [hSame] at hTriangle
    have hSmall := rowWeight_le_of_column_support c columns hColumnSupport a
    omega
  · intro b hb
    have hDistance := hA _ (hc b) hb
    have hTriangle := HammingWeight_add_le (columnRestriction b x) (columnRestriction b r)
    have hSame : columnRestriction b x + columnRestriction b r = columnRestriction b c := by
      rw [hParts, map_add]
      exact hCancel _ _
    rw [hSame] at hTriangle
    have hSmall := columnWeight_le_of_row_support r rows hRowSupport b
    omega
end QEC.Coding.QuantumTanner
