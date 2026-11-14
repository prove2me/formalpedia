-- Prove2me | solution 1 for avram_chat24_uniform_cell_cover_core
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T14:40:10.049192+00:00
-- url     : https://prove2.me/submissions/0252bceb-6b8b-495d-bfb8-80d201e4027a

import Mathlib

open scoped NNReal

noncomputable section

theorem solution (B : ℝ≥0) (hB : 0 < B) (n : ℕ)
    (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
    ∃ i : ℕ, i < n + 1 ∧
      B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((i + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by
  set N : ℕ := n + 1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set r : ℝ := (N : ℝ) * (t : ℝ) / (B : ℝ)
  have hr_pos : 0 < r := by
    dsimp [r]; positivity
  have hr_le : r ≤ (N : ℝ) := by
    dsimp [r]
    have htB' : (t : ℝ) ≤ (B : ℝ) := by exact_mod_cast htB
    calc (N : ℝ) * (t : ℝ) / (B : ℝ)
        ≤ (N : ℝ) * (B : ℝ) / (B : ℝ) := by gcongr
      _ = (N : ℝ) := by field_simp [ne_of_gt hBpos]
  have hceil_pos : 0 < ⌈r⌉₊ := (Nat.one_le_ceil_iff).2 hr_pos
  set k : ℕ := ⌈r⌉₊
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hceil_pos
  have hk : (↑(k - 1) : ℝ) < r ∧ r ≤ (k : ℝ) := (Nat.ceil_eq_iff hk0).1 (by simp [k])
  set i : ℕ := k - 1
  have hi_lt : i < N := by
    have hk_le : k ≤ N := by
      simpa [k] using (Nat.ceil_le.mpr hr_le)
    omega
  refine ⟨i, by simpa [N] using hi_lt, ?_, ?_⟩
  · have hir : (i : ℝ) < r := by simpa [i] using hk.1
    have hdiv : (B : ℝ) * (i : ℝ) / (N : ℝ) < (t : ℝ) := by
      have hi' : (i : ℝ) * (B : ℝ) < r * (B : ℝ) :=
        mul_lt_mul_of_pos_right hir hBpos
      have hrB : r * (B : ℝ) = (N : ℝ) * (t : ℝ) := by
        dsimp [r]; field_simp [ne_of_gt hBpos]
      rw [hrB] at hi'
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      calc (B : ℝ) * (i : ℝ) / (N : ℝ)
          = (i : ℝ) * (B : ℝ) / (N : ℝ) := by ring
        _ < (N : ℝ) * (t : ℝ) / (N : ℝ) :=
            div_lt_div_of_pos_right hi' hNpos
        _ = (t : ℝ) := by field_simp [hNne]
    exact_mod_cast hdiv
  · have hir : r ≤ ((i + 1 : ℕ) : ℝ) := by
      have hik : i + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hceil_pos)
      simpa [hik, i] using hk.2
    have hdiv : (t : ℝ) ≤ (B : ℝ) * ((i + 1 : ℕ) : ℝ) / (N : ℝ) := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hmul : (N : ℝ) * (t : ℝ) ≤ (B : ℝ) * ((i + 1 : ℕ) : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_right hir (le_of_lt hBpos)
        dsimp [r] at h1
        have hsimp : (N : ℝ) * (t : ℝ) / (B : ℝ) * (B : ℝ) = (N : ℝ) * (t : ℝ) := by
          field_simp [ne_of_gt hBpos]
        rw [hsimp] at h1
        nlinarith
      calc (t : ℝ)
          = (N : ℝ) * (t : ℝ) / (N : ℝ) := by field_simp [hNne]
        _ ≤ (B : ℝ) * ((i + 1 : ℕ) : ℝ) / (N : ℝ) :=
            div_le_div_of_nonneg_right hmul (le_of_lt hNpos)
    exact_mod_cast hdiv
