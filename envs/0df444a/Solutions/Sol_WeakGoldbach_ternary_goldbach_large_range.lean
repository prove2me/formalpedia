-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:31.898956+00:00
-- url     : https://prove2.me/submissions/030a3c52-faa4-4e54-97d4-73e2e20d876b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_primes_large_range
import Mathlib

theorem solution (n : Nat) (hodd : Odd n)
    (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  obtain ⟨p, q, r, hp, hq, hr, hp2, hq2, hr2, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_primes_large_range n hodd hlo
  refine ⟨p, q, r, hp, hq, hr, ?_, ?_, ?_, hsum⟩
  · exact hp.odd_iff.mpr (by omega)
  · exact hq.odd_iff.mpr (by omega)
  · exact hr.odd_iff.mpr (by omega)
