-- Prove2me | solution 23 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T16:53:18.630269+00:00
-- url     : https://prove2.me/submissions/3bedf3b9-4fe7-4c05-abbb-7e6b2eb9224b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

This splits the range at the `verified_three_primes_to_8875e30` ceiling rather
than reducing to a single conjecture, so it introduces no hypothesis that is
strictly harder than the target itself.

Below the ceiling the Proved-threshold `verified_three_primes_to_8875e30`
applies; above it, `n` exceeds `10^27`, so `three_odd_primes_ge_10pow27`
applies and returns three odd primes, which are in particular primes. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have key : ∀ (p q r : ℕ), Nat.Prime p → Nat.Prime q → Nat.Prime r → n = p + q + r →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨{p, q, r}, by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using hr
    · have hval : p + q + r = n := hsum.symm
      simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hval
  by_cases hprime : Nat.Prime n
  · exact WeakGoldbach.three_primes_of_prime n hprime
  · by_cases h3 : n = 3
    · subst h3
      exact WeakGoldbach.three_primes_three
    · by_cases h5 : n = 5
      · subst h5
        exact WeakGoldbach.three_primes_five
      · -- `Odd n` is opaque to `omega`, so expose it as the linear equation
        -- `n = 2 * k + 1`. Together with `1 < n`, `n ≠ 3` and `n ≠ 5` this
        -- gives `n ≥ 7`, which is the floor both children require. `hodd` is
        -- rebuilt as `hodd'` because the `obtain` above consumes it.
        obtain ⟨k, hk⟩ := hodd
        have hge7 : 7 ≤ n := by omega
        have hodd' : Odd n := ⟨k, hk⟩
        rcases le_total n 8875694145621773516800000000000 with hbig | hbig
        · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
            WeakGoldbach.verified_three_primes_to_8875e30 n hge7 hbig hodd'
          exact key p q r hp hq hr hsum
        · have hlo : 10 ^ 27 ≤ n := by
            have h1 : (10 : ℕ) ^ 27 = 1000000000000000000000000000 := by norm_num
            have h2 : 1000000000000000000000000000 < 8875694145621773516800000000000 := by
              norm_num
            omega
          obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
            WeakGoldbach.three_odd_primes_ge_10pow27 n hlo hodd'
          exact key p q r hp hq hr hsum

