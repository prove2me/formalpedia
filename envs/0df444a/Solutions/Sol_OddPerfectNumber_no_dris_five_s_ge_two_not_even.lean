-- Prove2me | solution 1 for OddPerfectNumber.no_dris_five_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:06:35.81908+00:00
-- url     : https://prove2.me/submissions/2ad82584-c56d-4540-a3bf-f9a4456a291a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_eq_three
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_ge_five

open OddPerfectNumber

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  intro hcon
  by_cases hs3 : s = 3
  · subst hs3
    exact no_dris_five_s_odd_eq_three p m 3 hp hp2 hp4 hm hpm rfl hcon
  -- NB: remote `omega` cannot use hypothesis-form `¬ Even s` (row 332 CE),
  -- so destructure parity to a linear witness first.
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hs_not_even
    have hs5 : 5 ≤ s := by omega
    exact no_dris_five_s_odd_ge_five p m s hp hp2 hp4 hm hpm hs_not_even hs5 hcon
