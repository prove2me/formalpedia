-- Prove2me | solution 1 for OddPerfectNumber.opnLeftRay_vieta_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:33:48.828297+00:00
-- url     : https://prove2.me/submissions/5379bf98-cd9c-4d9c-81e0-0cd87e401ee8

import Mathlib
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_opnLeftRay_pos_monotone
import Theorems.Thm_OddPerfectNumber_opnLeftRay_recurrence
import Theorems.Thm_OddPerfectNumber_vieta_phi5_other_root

open OddPerfectNumber

theorem solution (n : Nat) :
    opnLeftRay n ^ 2 + opnLeftRay n +
        opnLeftRay (n + 1) ^ 2 + opnLeftRay (n + 1) + 1 =
      9 * (opnLeftRay n * opnLeftRay (n + 1) - 1) := by
  induction n with
  | zero =>
      norm_num [opnLeftRay]
  | succ n ih =>
      have hprev := opnLeftRay_pos_monotone n
      have hnext := opnLeftRay_pos_monotone (n + 1)
      rcases hprev with ⟨hnpos, hnmono⟩
      rcases hnext with ⟨hn1pos, hn1mono⟩
      have hsym :
          opnLeftRay (n + 1) ^ 2 + opnLeftRay (n + 1) +
              opnLeftRay n ^ 2 + opnLeftRay n + 1 =
            9 * (opnLeftRay (n + 1) * opnLeftRay n - 1) := by
        calc
          opnLeftRay (n + 1) ^ 2 + opnLeftRay (n + 1) +
                opnLeftRay n ^ 2 + opnLeftRay n + 1 =
              opnLeftRay n ^ 2 + opnLeftRay n +
                opnLeftRay (n + 1) ^ 2 + opnLeftRay (n + 1) + 1 := by
            ring
          _ = 9 * (opnLeftRay n * opnLeftRay (n + 1) - 1) := ih
          _ = 9 * (opnLeftRay (n + 1) * opnLeftRay n - 1) := by
            rw [mul_comm (opnLeftRay n) (opnLeftRay (n + 1))]
      obtain ⟨z, hzpos, hzrel, hzprod, hzeq⟩ :=
        vieta_phi5_other_root (opnLeftRay (n + 1)) (opnLeftRay n) 9
          hn1pos hnpos hsym
      have hrec := opnLeftRay_recurrence n
      have hz : z = opnLeftRay (n + 2) := by
        omega
      simpa [hz, Nat.add_assoc] using hzeq
