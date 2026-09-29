-- Prove2me | solution 1 for OddPerfectNumber.opnLeftRay_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T09:04:39.540854+00:00
-- url     : https://prove2.me/submissions/ddbff7bc-cfa7-418c-bc83-ce83d4038397

import Mathlib
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_opnLeftRay_pos_monotone

open OddPerfectNumber

theorem solution (n : Nat) :
    opnLeftRay (n + 2) + opnLeftRay n + 1 =
      9 * opnLeftRay (n + 1) := by
  have hn := opnLeftRay_pos_monotone n
  have hn1 := opnLeftRay_pos_monotone (n + 1)
  rcases hn with ⟨hnpos, hnmono⟩
  rcases hn1 with ⟨hn1pos, hn1mono⟩
  change
    (9 * opnLeftRay (n + 1) - opnLeftRay n - 1) +
        opnLeftRay n + 1 =
      9 * opnLeftRay (n + 1)
  omega
