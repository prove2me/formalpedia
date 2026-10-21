-- Prove2me | solution 1 for PosetSecretary.ProxyLabel.exp_neg_c_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:06:36.347634+00:00
-- url     : https://prove2.me/submissions/f8348588-42df-4f59-b11d-daf4f49b7141

import Mathlib
set_option autoImplicit false

theorem solution (ω ω' : ℕ) (c : ℝ) (hc : 1 ≤ c) (hω' : (ω : ℝ) / c ≤ ω') :
    1 / (Real.exp c * (ω' + 1)) ≤ (1 / (ω' + 1 : ℝ)) * (1 - 1 / (ω' + 1 : ℝ)) ^ ω := by
  have hc0 : 0 < c := by linarith
  have hωc : (ω : ℝ) ≤ c * ω' := by
    rw [div_le_iff₀ hc0] at hω'; linarith
  have hm : (0 : ℝ) < ω' + 1 := by positivity
  have hexp : 0 < Real.exp c := Real.exp_pos c
  have key : Real.exp (-c) ≤ (1 - 1 / (ω' + 1 : ℝ)) ^ ω := by
    rcases Nat.eq_zero_or_pos ω' with h0 | hpos
    · subst h0
      have : (ω : ℝ) ≤ 0 := by simpa using hωc
      have hw : ω = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
      subst hw
      rw [pow_zero]
      exact (Real.exp_le_one_iff).2 (by linarith)
    · have hp : (0 : ℝ) < ω' := by exact_mod_cast hpos
      have hy : 0 < 1 - 1 / ((ω' : ℝ) + 1) := by
        rw [sub_pos, div_lt_one hm]; linarith
      have hlog : -1 / (ω' : ℝ) ≤ Real.log (1 - 1 / ((ω' : ℝ) + 1)) := by
        have := Real.one_sub_inv_le_log_of_pos hy
        have e : 1 - (1 - 1 / ((ω' : ℝ) + 1))⁻¹ = -1 / ω' := by
          have h3 : (1 - 1 / ((ω' : ℝ) + 1)) = ω' / (ω' + 1) := by
            field_simp
            ring
          rw [h3, inv_div]
          field_simp
          ring
        rw [e] at this; exact this
      rw [← Real.exp_log hy, ← Real.exp_nat_mul]
      · apply Real.exp_le_exp.2
        have h1 : (ω : ℝ) * (-1 / ω') ≤ ω * Real.log (1 - 1 / ((ω' : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        have h2 : -c ≤ (ω : ℝ) * (-1 / ω') := by
          have : (ω : ℝ) * (-1 / ω') = -((ω : ℝ) / ω') := by ring
          rw [this, neg_le_neg_iff, div_le_iff₀ hp]; linarith
        linarith
  have hx : 0 < 1 / ((ω' : ℝ) + 1) := by positivity
  calc 1 / (Real.exp c * (ω' + 1)) = (1 / ((ω' : ℝ) + 1)) * Real.exp (-c) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left key hx.le
