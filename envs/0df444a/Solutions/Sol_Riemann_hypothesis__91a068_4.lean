-- Prove2me | solution 4 for Riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T15:05:27.564477+00:00
-- url     : https://prove2.me/submissions/d4d6bb6f-6b60-4867-98da-217d53f3da34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_rh_zeta_zero_free_right_half
import Theorems.Thm_rh_zeta_zero_free_left_half
import Mathlib

theorem solution : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs_pos hs_lt_one hz
  by_contra hne
  have hlt_or_ge : s.re < 1 / 2 ∨ 1 / 2 ≤ s.re := by
    apply lt_or_ge
  cases hlt_or_ge with
  | inl hlt =>
    have hne_zero := rh_zeta_zero_free_left_half s hs_pos hlt
    exact hne_zero hz
  | inr hge =>
    have hlt_or_eq : 1 / 2 < s.re ∨ 1 / 2 = s.re := by
      apply lt_or_eq_of_le
      exact hge
    cases hlt_or_eq with
    | inl hgt =>
      have hne_zero := rh_zeta_zero_free_right_half s hgt hs_lt_one
      exact hne_zero hz
    | inr heq =>
      exact hne heq.symm
