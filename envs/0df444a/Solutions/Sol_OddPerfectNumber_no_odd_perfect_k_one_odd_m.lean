-- Prove2me | solution 1 for OddPerfectNumber.no_odd_perfect_k_one_odd_m
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T23:26:21.633489+00:00
-- url     : https://prove2.me/submissions/cd8c7557-3ae2-45b7-82c4-df3d2d2648da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_sigma_bridge
import Theorems.Thm_OddPerfectNumber_k_one_sigma_diophantine

open OddPerfectNumber

theorem solution (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m) : n != p * m ^ 2 := by
  -- Boolean goal: prove the `≠` version, then convert with `bne_iff_ne`.
  suffices hne : n ≠ p * m ^ 2 by
    exact bne_iff_ne.mpr hne
  intro h
  have e := k_one_sigma_bridge n p m hn hodd hp hp4 hpm hm_odd h
  exact k_one_sigma_diophantine p m hp hp4 hpm hm_odd e
