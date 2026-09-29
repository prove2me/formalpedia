-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:31.430217+00:00
-- url     : https://prove2.me/submissions/7c3dba25-7a03-4850-89f3-3cd3703ef13c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_candidates_v4

open OddPerfectNumber

theorem solution (D p q4 : Nat)
  (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
  (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
  (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
  (hq4dvd : q4 ∣ D) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
    (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 427 ∧ p = 853 ∧ q4 = 61) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨
    (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) ∨
    (D = 649 ∧ p = 1297 ∧ q4 = 59) :=
  OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v4 D p q4 hDlow hDhigh hp hp4 hp_eq hq4 hq4gt hq4le hq4dvd
