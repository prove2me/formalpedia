-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.touching_interval_sets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:10:18.607303+00:00
-- url     : https://prove2.me/submissions/5e8d8eee-d954-4757-b86b-29d14fe50bc5

import Mathlib

theorem X7ti_main (K0 K1 : Set ℝ) (hcover : K0 ∪ K1 = Set.Icc 0 1)
    (hzero : 0 ∈ K0) (hone : 1 ∈ K1) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ u ∈ K0, ∃ v ∈ K1, 0 ≤ v - u ∧ v - u ≤ delta := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hstep : 1 / (N : ℝ) ≤ delta := by
    rw [div_le_iff₀ hNpos]; rw [div_lt_iff₀ hdelta] at hN; linarith
  have hex : ∃ k : ℕ, (k : ℝ) / N ∈ K1 := ⟨N, by rw [div_self hNpos.ne']; exact hone⟩
  classical
  let j := Nat.find hex
  have hj : (j : ℝ) / N ∈ K1 := Nat.find_spec hex
  have hjN : j ≤ N := Nat.find_min' hex (by rw [div_self hNpos.ne']; exact hone)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · refine ⟨0, hzero, 0, ?_, by simp, by simp; exact hdelta.le⟩
    have := hj; rw [h0] at this; simpa using this
  · have hprev : ((j - 1 : ℕ) : ℝ) / N ∉ K1 := Nat.find_min hex (by omega)
    have hmem : ((j - 1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hNpos]; exact_mod_cast (by omega : j - 1 ≤ N)
    rw [← hcover] at hmem
    have hK0 : ((j - 1 : ℕ) : ℝ) / N ∈ K0 := hmem.resolve_right hprev
    refine ⟨_, hK0, _, hj, ?_, ?_⟩
    · have : ((j - 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j 1
      rw [sub_nonneg]; exact div_le_div_of_nonneg_right this hNpos.le
    · have e : (j : ℝ) / N - ((j - 1 : ℕ) : ℝ) / N = 1 / N := by
        rw [Nat.cast_sub (by omega)]; field_simp; ring
      rw [e]; exact hstep

theorem solution (K0 K1 : Set ℝ) (hcover : K0 ∪ K1 = Set.Icc 0 1)
    (hzero : 0 ∈ K0) (hone : 1 ∈ K1) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ u ∈ K0, ∃ v ∈ K1, 0 ≤ v - u ∧ v - u ≤ delta :=
  X7ti_main K0 K1 hcover hzero hone delta hdelta
