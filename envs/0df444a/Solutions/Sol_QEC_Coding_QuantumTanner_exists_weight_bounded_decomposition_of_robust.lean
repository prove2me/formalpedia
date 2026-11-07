-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_weight_bounded_decomposition_of_robust
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:10:44.480427+00:00
-- url     : https://prove2.me/submissions/8800093c-9281-4b25-8c77-daf829e862be

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorApproximation
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_weight_bounded_decomposition_of_half_distance_cover


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w : Nat) (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hRobust : IsRobust CA CB w) (hBudget : 2 * w ≤ dA * dB)
    (y : Word (ZMod 2) (A × B))
    (hy : y ∈ (dualTensorCode CA CB).carrier) (hWeight : HammingWeight y ≤ w) :
    ∃ r c : Word (ZMod 2) (A × B),
      r ∈ (rowCode (A := A) CB).carrier ∧
      c ∈ (columnCode (B := B) CA).carrier ∧
      y = r + c ∧ HammingWeight r ≤ HammingWeight y ∧
        HammingWeight c ≤ HammingWeight y := by
  obtain ⟨rows, columns, hCover, hRows, hColumns⟩ :=
    hRobust dA dB hA hB y hy hWeight
  obtain ⟨a, ha, ha0, hwa, hMinA⟩ := hA
  obtain ⟨b, hb, hb0, hwb, hMinB⟩ := hB
  have hPosA : 0 < dA := by
    rw [← hwa]
    exact Nat.pos_of_ne_zero fun hz => ha0 ((HammingWeight_eq_zero_iff a).mp hz)
  have hPosB : 0 < dB := by
    rw [← hwb]
    exact Nat.pos_of_ne_zero fun hz => hb0 ((HammingWeight_eq_zero_iff b).mp hz)
  have hRowsMul := (Nat.le_div_iff_mul_le hPosB).mp hRows
  have hColumnsMul := (Nat.le_div_iff_mul_le hPosA).mp hColumns
  apply exists_weight_bounded_decomposition_of_half_distance_cover
    CA CB dA dB hMinA hMinB hPosA hPosB y hy rows columns ?_ ?_ hCover
  · nlinarith
  · nlinarith
end QEC.Coding.QuantumTanner
