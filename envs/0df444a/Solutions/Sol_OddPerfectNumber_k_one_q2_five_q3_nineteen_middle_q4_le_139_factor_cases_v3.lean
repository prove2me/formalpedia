-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:21:35.738888+00:00
-- url     : https://prove2.me/submissions/05f19d7a-22fd-4d8e-a423-bb939f1e9d1d

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v5

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hrel : D * sigma = p * m ^ 2) (hDlow : 142 ≤ D) (hDhigh : D < 225) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4le : q4 ≤ 139) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    (D = 159 ∧ q4 = 53 ∧ p = 317) ∨ (D = 177 ∧ q4 = 59 ∧ p = 353) ∨ (D = 201 ∧ q4 = 67 ∧ p = 401) ∨ (D = 205 ∧ q4 = 41 ∧ p = 409) :=
  OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_factor_cases_v5 m a b c e D p q4 sigma hfac hrel hDlow hDhigh hp hp_eq hq4prime hq4gt hq4le hDsupport
