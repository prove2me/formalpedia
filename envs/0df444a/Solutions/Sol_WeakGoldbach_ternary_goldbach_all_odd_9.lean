-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_all_odd_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T13:10:26.926727+00:00
-- url     : https://prove2.me/submissions/e5ef0f87-1bfa-4a74-bafc-df6fbe589856
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

-- Reduction of the correctly-stated Helfgott sibling
-- `WeakGoldbach.ternary_goldbach_all_odd_9`, whose bound is `9 <= n`.
--
-- Why this target matters.  The catalogue also holds
-- `WeakGoldbach.ternary_goldbach_all_odd` with the bound `5 < n`, and that record
-- is `Disproved`: the smallest sum of three odd primes is 3 + 3 + 3 = 9, so the
-- value n = 7 is a genuine counterexample to the `5 < n` bound.  The `_9`
-- record is the corrected form and is the one this candidate reduces.  It had
-- zero registered decompositions, so a fresh reduction is admissible.
--
-- Why the split is exact.  Both children conclude with three *odd* primes, which
-- is precisely the target's conclusion, so no parity reconstruction is needed
-- and no multiset packaging is needed.  The two children tile the range with no
-- gap and no overlap:
--
--   * `verified_three_odd_primes_to_8875e30` covers 9 <= n <= 8875694145621773516800000000000
--   * `three_odd_primes_ge_10pow27`          covers 10^27 <= n
--
-- The crossover is consistent because 10^27 = 1000000000000000000000000000
-- <= 8875694145621773516800000000000, so the verified range reaches past the
-- point where the analytic band begins; the union is therefore all of n >= 9
-- and the two bands merely overlap on [10^27, 8.875...e30].

open WeakGoldbach

theorem solution (n : Nat) (hlo : 9 <= n) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  rcases Nat.lt_or_ge n (10 ^ 27) with hlt27 | hge27
  · -- `hlt27 : n < 10^27` and `hlo : 9 <= n` place `n` inside the verified band,
    -- once the band's upper constant is seen to exceed `10^27`.
    have hhi : n <= 8875694145621773516800000000000 := by
      have hc : (10 ^ 27 : Nat) <= 8875694145621773516800000000000 := by norm_num
      omega
    exact WeakGoldbach.verified_three_odd_primes_to_8875e30 n hlo hhi hodd
  · -- `hge27 : 10^27 <= n` is exactly the second band's hypothesis.
    exact WeakGoldbach.three_odd_primes_ge_10pow27 n hge27 hodd
