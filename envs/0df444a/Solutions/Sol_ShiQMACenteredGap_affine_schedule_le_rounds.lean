-- Prove2me | solution 1 for ShiQMACenteredGap.affine_schedule_le_rounds
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T01:06:08.724081+00:00
-- url     : https://prove2.me/submissions/78c5f067-0866-434b-a81f-376ce82c378c

import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution (A D n : Nat) :
    A + D * (Nat.log 2 (n + 1) + 1) ≤ rounds (schedulePolynomial A D) n := by
  have hd : (schedulePolynomial A D).natDegree = D := by
    exact Polynomial.natDegree_monomial_eq D (pow_ne_zero _ (by decide))
  have he : (schedulePolynomial A D).eval 1 = 2 ^ A := by
    simp [schedulePolynomial]
  have hl : A ≤ Nat.log 2 (2 ^ A + 1) :=
    Nat.le_log_of_pow_le (by decide) (Nat.le_succ _)
  dsimp [rounds, exponentBudget]
  rw [hd, he]
  omega
