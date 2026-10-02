-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_order_dvd_pow_card_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:46:16.410986+00:00
-- url     : https://prove2.me/submissions/c796cf83-b149-4cdf-8a67-6e0e83196a4c

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

theorem solution {p t : Nat} (hp : p.Prime)
    (hpt : Not (Dvd.dvd p t))
    (hodd : Odd (orderOf (t : ZMod p))) :
    (t : ZMod p) ^ (orderOf (t : ZMod p)) = 1 :=
  pow_orderOf_eq_one (t : ZMod p)
