-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:32.795689+00:00
-- url     : https://prove2.me/submissions/98c26224-2e22-4f1e-b4ef-c687ebcb1590

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2

open OddPerfectNumber

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 19 ^ i :=
  OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_v2 e
