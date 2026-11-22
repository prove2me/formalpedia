-- Prove2me | solution 5 for Riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T15:14:12.330106+00:00
-- url     : https://prove2.me/submissions/49b1e807-4fab-448c-b4f9-4b4f09bbcaf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemannZeta_eq_zero_re
import Mathlib

theorem solution : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hpos hlt hz
  have h_trivial : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    intro hn
    rcases hn with ⟨n, hn⟩
    rw [hn] at hpos
    have h_re : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.ext_iff, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
      <;> norm_cast
      <;> ring
    rw [h_re] at hpos
    have h_neg : -2 * ((n : ℝ) + 1) < 0 := by
      norm_cast
      <;> linarith
    linarith
  have h_ne_one : s ≠ 1 := by
    intro h_eq
    rw [h_eq] at hlt
    norm_num at hlt
  exact riemannZeta_eq_zero_re s hz h_trivial h_ne_one
