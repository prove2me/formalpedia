-- Prove2me | solution 6 for Riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T15:24:15.045802+00:00
-- url     : https://prove2.me/submissions/4b84f112-863f-4cbe-adef-f434684a4218
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemannZeta_eq_zero_re
import Mathlib

theorem solution : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hpos hlt hz
  have h_trivial : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    intro hn
    rcases hn with ⟨n, hn⟩
    have h_re : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp [Complex.re, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
      <;> norm_cast
      <;> ring
    rw [h_re] at hpos
    have h_neg : -2 * ((n : ℝ) + 1) < 0 := by
      have h_n_pos : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      linarith
    linarith
  have h_ne_one : s ≠ 1 := by
    intro h_eq
    rw [h_eq] at hlt
    norm_num at hlt
  exact riemannZeta_eq_zero_re s hz h_trivial h_ne_one
