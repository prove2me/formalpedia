-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_primes_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:10:20.668908+00:00
-- url     : https://prove2.me/submissions/bf0e42a3-6a0c-49fc-acb3-0fd10551ac33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100
import Mathlib

theorem solution (n : Nat) (hodd : Odd n)
    (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (2 < p) (And (2 < q) (And (2 < r) (n = p + q + r)))))) := by
  obtain ⟨p, q, r, hp, hq, hr, hpodd, hqodd, hrodd, hsum⟩ :=
    WeakGoldbach.three_odd_primes_ge_exp3100 n hlo hodd
  refine ⟨p, q, r, hp, hq, hr, ?_, ?_, ?_, hsum⟩
  · have hpge : 2 ≤ p := hp.two_le
    have hpne : p ≠ 2 := by
      intro heq
      subst p
      norm_num at hpodd
    omega
  · have hqge : 2 ≤ q := hq.two_le
    have hqne : q ≠ 2 := by
      intro heq
      subst q
      norm_num at hqodd
    omega
  · have hrge : 2 ≤ r := hr.two_le
    have hrne : r ≠ 2 := by
      intro heq
      subst r
      norm_num at hrodd
    omega
