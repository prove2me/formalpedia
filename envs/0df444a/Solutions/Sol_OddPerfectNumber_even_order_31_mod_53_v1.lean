-- Prove2me | solution 1 for OddPerfectNumber.even_order_31_mod_53_v1
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:19:39.792202+00:00
-- url     : https://prove2.me/submissions/b949c6bd-f968-4644-84a7-a01361ca88cf

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_order_31_mod_53_v2

open OddPerfectNumber

theorem solution :
    Even (orderOf (31 : ZMod 53)) :=
  OddPerfectNumber.even_order_31_mod_53_v2
