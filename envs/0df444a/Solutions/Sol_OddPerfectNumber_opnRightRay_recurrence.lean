-- Prove2me | solution 1 for OddPerfectNumber.opnRightRay_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:03:33.802374+00:00
-- url     : https://prove2.me/submissions/83d092d9-cb5b-44d9-bb07-7936e8ab75f7

import Mathlib
import Definitions.Def_opnRightRay
import Theorems.Thm_OddPerfectNumber_opnRightRay_pos_monotone

open OddPerfectNumber

theorem solution (n : Nat) :
    opnRightRay (n + 2) + opnRightRay n + 1 =
      9 * opnRightRay (n + 1) := by
  have hn := opnRightRay_pos_monotone n
  have hn1 := opnRightRay_pos_monotone (n + 1)
  rcases hn with ⟨hnpos, hnmono⟩
  rcases hn1 with ⟨hn1pos, hn1mono⟩
  change
    (9 * opnRightRay (n + 1) - opnRightRay n - 1) +
        opnRightRay n + 1 =
      9 * opnRightRay (n + 1)
  omega
