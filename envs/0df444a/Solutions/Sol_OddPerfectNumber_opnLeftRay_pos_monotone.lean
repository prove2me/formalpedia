-- Prove2me | solution 1 for OddPerfectNumber.opnLeftRay_pos_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:02:20.678858+00:00
-- url     : https://prove2.me/submissions/c0993658-ddb3-49c3-8dc9-9b5c4966fdbc

import Mathlib
import Definitions.Def_opnLeftRay

theorem solution (n : Nat) :
    0 < opnLeftRay n ∧ opnLeftRay n ≤ opnLeftRay (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          norm_num [opnLeftRay]
      | succ n =>
          cases n with
          | zero =>
              norm_num [opnLeftRay]
          | succ n =>
              have hn := ih n (by omega)
              have hn1 := ih (n + 1) (by omega)
              rcases hn with ⟨hnpos, hnmono⟩
              rcases hn1 with ⟨hn1pos, hn1mono⟩
              change
                0 < 9 * opnLeftRay (n + 1) - opnLeftRay n - 1 ∧
                  9 * opnLeftRay (n + 1) - opnLeftRay n - 1 ≤
                    9 * (9 * opnLeftRay (n + 1) - opnLeftRay n - 1) -
                      opnLeftRay (n + 1) - 1
              omega
