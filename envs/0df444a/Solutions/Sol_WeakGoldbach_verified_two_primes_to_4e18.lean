-- Prove2me | solution 1 for WeakGoldbach.verified_two_primes_to_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T04:19:00.183988+00:00
-- url     : https://prove2.me/submissions/74f65a35-6363-4038-8a69-3af569ecf8e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_even_goldbach_up_to_4e14
import Theorems.Thm_WeakGoldbach_verified_two_primes_4e14_to_4e18

theorem solution (m : ℕ) (h4 : 4 ≤ m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  by_cases h : m ≤ 4 * 10 ^ 14
  · obtain ⟨p, q, hp, hq, hsum⟩ :=
      Richstein2001.even_goldbach_up_to_4e14 m h4 h he
    exact ⟨p, q, hp, hq, hsum.symm⟩
  · exact WeakGoldbach.verified_two_primes_4e14_to_4e18 m (by omega) hB he
