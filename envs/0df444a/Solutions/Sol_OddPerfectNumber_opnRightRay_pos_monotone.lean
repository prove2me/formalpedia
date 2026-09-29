-- Prove2me | solution 1 for OddPerfectNumber.opnRightRay_pos_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:02:00.472231+00:00
-- url     : https://prove2.me/submissions/b1baf35b-5d3d-49cd-825e-505340a31636

import Mathlib
import Definitions.Def_opnRightRay

theorem solution (n : Nat) :
    0 < opnRightRay n ∧ opnRightRay n ≤ opnRightRay (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          norm_num [opnRightRay]
      | succ n =>
          cases n with
          | zero =>
              norm_num [opnRightRay]
          | succ n =>
              have hn := ih n (by omega)
              have hn1 := ih (n + 1) (by omega)
              rcases hn with ⟨hnpos, hnmono⟩
              rcases hn1 with ⟨hn1pos, hn1mono⟩
              change
                0 < 9 * opnRightRay (n + 1) - opnRightRay n - 1 ∧
                  9 * opnRightRay (n + 1) - opnRightRay n - 1 ≤
                    9 * (9 * opnRightRay (n + 1) - opnRightRay n - 1) -
                      opnRightRay (n + 1) - 1
              omega
