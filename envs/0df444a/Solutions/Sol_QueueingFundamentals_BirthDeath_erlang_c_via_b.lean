-- Prove2me | solution 1 for QueueingFundamentals.BirthDeath.erlang_c_via_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:18:06.860983+00:00
-- url     : https://prove2.me/submissions/932823a9-edca-4a26-a35b-9f0c98e40fad

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

set_option autoImplicit false

open QueueingFundamentals.BirthDeath in
theorem solution (c : ℕ) (r : ℝ) (hr : 0 < r) (hrc : r < c) :
    erlangC c r = (c : ℝ) * erlangB c r / ((c : ℝ) - r + r * erlangB c r) := by
  have hc : (0 : ℝ) < c := lt_trans hr hrc
  have hcr : (0 : ℝ) < (c : ℝ) - r := by linarith
  have hcN : 0 < c := by exact_mod_cast hc
  have ha : 0 < r ^ c / (c.factorial : ℝ) := by positivity
  have hS : 0 < ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) := by
    apply Finset.sum_pos
    · intro i _; positivity
    · exact ⟨0, Finset.mem_range.mpr hcN⟩
  unfold erlangC erlangB
  rw [Finset.sum_range_succ]
  set a := r ^ c / (c.factorial : ℝ) with ha_def
  set S := ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ) with hS_def
  have hfac : (0 : ℝ) < (c.factorial : ℝ) := by positivity
  have h1 : r ^ c / ((c.factorial : ℝ) * (1 - r / c)) = a * c / (c - r) := by
    rw [ha_def]; field_simp
  rw [h1]
  have hT : 0 < S + a := by linarith
  have hden : 0 < (c : ℝ) - r + r * (a / (S + a)) := by
    have : 0 < r * (a / (S + a)) := by positivity
    linarith
  rw [div_eq_div_iff (by positivity) hden.ne']
  field_simp
  ring
