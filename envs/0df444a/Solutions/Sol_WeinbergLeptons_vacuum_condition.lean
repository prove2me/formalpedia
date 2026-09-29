-- Prove2me | solution 1 for WeinbergLeptons.vacuum_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T00:30:11.847003+00:00
-- url     : https://prove2.me/submissions/2c241f71-5a15-4af9-983e-0a1b2a9f15c2

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (M1 h lam : ℝ) (hh : h ≠ 0) (hlam : lam ≠ 0) :
    deriv (scalarPotentialTerm M1 h) lam = 0 ↔ lam ^ 2 = M1 ^ 2 / (2 * h) := by
  have hD : HasDerivAt (scalarPotentialTerm M1 h)
      (-M1 ^ 2 * ((2 : ℕ) * lam ^ (2 - 1)) + h * ((4 : ℕ) * lam ^ (4 - 1))) lam := by
    have h1 := (hasDerivAt_pow 2 lam).const_mul (-M1 ^ 2)
    have h2 := (hasDerivAt_pow 4 lam).const_mul h
    exact h1.add h2
  have hd : deriv (scalarPotentialTerm M1 h) lam = -M1 ^ 2 * (2 * lam) + h * (4 * lam ^ 3) := by
    rw [hD.deriv]; norm_num
  rw [hd]
  have h2h : (2 * h) ≠ 0 := mul_ne_zero two_ne_zero hh
  constructor
  · intro H
    have e : lam * (2 * (lam ^ 2 * (2 * h) - M1 ^ 2)) = 0 := by linear_combination H
    rcases mul_eq_zero.1 e with h0 | h0
    · exact absurd h0 hlam
    · rw [eq_div_iff h2h]; linarith
  · intro H
    have e : lam ^ 2 * (2 * h) = M1 ^ 2 := by rw [H]; field_simp
    linear_combination (2 * lam) * e
