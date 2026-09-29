-- Prove2me | solution 2 for OddPerfectNumber.no_odd_perfect_k_one_odd_m
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:40:50.364164+00:00
-- url     : https://prove2.me/submissions/a0704f61-92a3-474a-82d9-42dcf04f4cfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_sigma_bridge
import Theorems.Thm_OddPerfectNumber_k_one_sigma_diophantine

theorem _root_.solution (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m) :
    n != p * m ^ 2 := by
  simp only [bne_iff_ne, ne_eq]
  intro h
  exact OddPerfectNumber.k_one_sigma_diophantine p m hp hp4 hpm hm_odd
    (OddPerfectNumber.k_one_sigma_bridge n p m hn hodd hp hp4 hpm hm_odd h)

#print axioms solution
