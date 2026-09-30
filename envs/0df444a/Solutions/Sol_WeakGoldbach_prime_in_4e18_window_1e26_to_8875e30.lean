-- Prove2me | solution 1 for WeakGoldbach.prime_in_4e18_window_1e26_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:28:02.354869+00:00
-- url     : https://prove2.me/submissions/14f04223-a2ed-4a86-9790-c9a6dd07f7ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_prime_bracket_gap_lt_4e18
import Mathlib

theorem solution (x : Nat)
    (hxl : 10 ^ 26 ≤ x)
    (hx : x ≤ 8875694145621773516800000000000 - 4 * 10 ^ 18) :
    ∃ p : Nat, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  obtain ⟨p, q, hp, hq, hpx, hxq, hgap⟩ :=
    WeakGoldbach.prime_bracket_gap_lt_4e18 x hxl hx
  have hpq : p ≤ q := le_trans hpx (Nat.le_of_lt hxq)
  have hq_lt_p : q < p + 4 * 10 ^ 18 := by
    have h := Nat.add_lt_add_right hgap p
    calc
      q = (q - p) + p := (Nat.sub_add_cancel hpq).symm
      _ < 4 * 10 ^ 18 + p := h
      _ = p + 4 * 10 ^ 18 := Nat.add_comm _ _
  refine ⟨q, hxq, ?_, hq⟩
  exact lt_of_lt_of_le hq_lt_p (Nat.add_le_add_right hpx _)
