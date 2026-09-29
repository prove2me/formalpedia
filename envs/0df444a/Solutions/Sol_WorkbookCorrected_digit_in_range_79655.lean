-- Prove2me | solution 1 for WorkbookCorrected.digit_in_range_79655
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:50:53.495973+00:00
-- url     : https://prove2.me/submissions/96544402-f65d-4c22-aa72-763ba96dfb53

import Mathlib

theorem solution : ∀ x ∈ Finset.Icc 101 2001, ∃ y ∈ Finset.Icc 0 9, y ∈ (Nat.digits 10 x) := by
  intro x hx
  have hx0 : x ≠ 0 := by
    simp only [Finset.mem_Icc] at hx
    omega
  have hpos : 0 < (Nat.digits 10 x).length :=
    List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hx0)
  obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos hpos
  refine ⟨y, ?_, hy⟩
  have := Nat.digits_lt_base (by norm_num) hy
  simp only [Finset.mem_Icc]
  omega
