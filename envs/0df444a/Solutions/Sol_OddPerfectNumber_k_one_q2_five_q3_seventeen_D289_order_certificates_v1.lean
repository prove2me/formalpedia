-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order_certificates_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T21:04:56.579813+00:00
-- url     : https://prove2.me/submissions/ceeb9eb4-659b-4c28-a8f7-78b00f5d7305

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order31_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order61_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order151_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order181_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order211_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order241_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order271_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order331_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order421_v1

open OddPerfectNumber

theorem solution :
    orderOf (3 : ZMod 31) = 30 ∧ orderOf (3 : ZMod 61) = 10 ∧
      orderOf (3 : ZMod 151) = 50 ∧ orderOf (3 : ZMod 181) = 45 ∧
      orderOf (3 : ZMod 211) = 210 ∧ orderOf (3 : ZMod 241) = 120 ∧
      orderOf (3 : ZMod 271) = 30 ∧ orderOf (3 : ZMod 331) = 330 ∧
      orderOf (3 : ZMod 421) = 105 :=
  ⟨k_one_q2_five_q3_seventeen_D289_order31_v2,
    k_one_q2_five_q3_seventeen_D289_order61_v1,
    k_one_q2_five_q3_seventeen_D289_order151_v1,
    k_one_q2_five_q3_seventeen_D289_order181_v1,
    k_one_q2_five_q3_seventeen_D289_order211_v1,
    k_one_q2_five_q3_seventeen_D289_order241_v1,
    k_one_q2_five_q3_seventeen_D289_order271_v1,
    k_one_q2_five_q3_seventeen_D289_order331_v1,
    k_one_q2_five_q3_seventeen_D289_order421_v1⟩
