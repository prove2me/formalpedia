-- Prove2me | solution 1 for OddPerfectNumber.opnRightRay_vieta_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:07:37.800909+00:00
-- url     : https://prove2.me/submissions/5e785e8f-db6f-42c7-81c6-d66eead59a1c

import Mathlib
import Definitions.Def_opnRightRay
import Theorems.Thm_OddPerfectNumber_opnRightRay_pos_monotone
import Theorems.Thm_OddPerfectNumber_opnRightRay_recurrence
import Theorems.Thm_OddPerfectNumber_vieta_phi5_other_root

open OddPerfectNumber

theorem solution (n : Nat) :
    opnRightRay n ^ 2 + opnRightRay n +
        opnRightRay (n + 1) ^ 2 + opnRightRay (n + 1) + 1 =
      9 * (opnRightRay n * opnRightRay (n + 1) - 1) := by
  induction n with
  | zero =>
      norm_num [opnRightRay]
  | succ n ih =>
      have hprev := opnRightRay_pos_monotone n
      have hnext := opnRightRay_pos_monotone (n + 1)
      rcases hprev with ⟨hnpos, hnmono⟩
      rcases hnext with ⟨hn1pos, hn1mono⟩
      have hsym :
          opnRightRay (n + 1) ^ 2 + opnRightRay (n + 1) +
              opnRightRay n ^ 2 + opnRightRay n + 1 =
            9 * (opnRightRay (n + 1) * opnRightRay n - 1) := by
        calc
          opnRightRay (n + 1) ^ 2 + opnRightRay (n + 1) +
                opnRightRay n ^ 2 + opnRightRay n + 1 =
              opnRightRay n ^ 2 + opnRightRay n +
                opnRightRay (n + 1) ^ 2 + opnRightRay (n + 1) + 1 := by
            ring
          _ = 9 * (opnRightRay n * opnRightRay (n + 1) - 1) := ih
          _ = 9 * (opnRightRay (n + 1) * opnRightRay n - 1) := by
            rw [mul_comm (opnRightRay n) (opnRightRay (n + 1))]
      obtain ⟨z, hzpos, hzrel, hzprod, hzeq⟩ :=
        vieta_phi5_other_root (opnRightRay (n + 1)) (opnRightRay n) 9
          hn1pos hnpos hsym
      have hrec := opnRightRay_recurrence n
      have hz : z = opnRightRay (n + 2) := by
        omega
      simpa [hz, Nat.add_assoc] using hzeq
