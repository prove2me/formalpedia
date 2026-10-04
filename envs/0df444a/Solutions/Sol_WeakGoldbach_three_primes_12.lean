-- Prove2me | solution 12 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T10:34:35.836244+00:00
-- url     : https://prove2.me/submissions/2dc1347e-25eb-4ada-86ff-a9e66e79628a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

set_option maxRecDepth 10000 in
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- Variant V. Builds on 5568 (SKETCH_ACCEPTED) but reaches the upper band
  -- through `three_odd_primes_ge_10pow27` at this mathlib revision, which is
  -- the same statement as the Helfgott child but without the `exp 3100`
  -- comparison anywhere in the dependency chain.
  --
  -- `sum` is closed with `add_assoc` in the simp set (fault 3), `hodd` is
  -- copied before being destructed (fault 2), and parity enters `omega` as the
  -- equation `hk : n = 2*k + 1` rather than as the structure `Odd n`
  -- (fault 4, the blocker in 5557 / 5561).
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + (q + r) = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨p ::ₘ q ::ₘ r ::ₘ (0 : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with ht | ht
      · exact ht ▸ hp
      · rcases Multiset.mem_cons.mp ht with ht | ht
        · exact ht ▸ hq
        · rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ hr
          · exact absurd ht (by simp)
    · simpa only [Multiset.sum_cons, Multiset.sum_zero, add_zero, add_assoc] using hsum
  have hodd' : Odd n := hodd
  obtain ⟨k, hk⟩ := hodd'
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · -- `hk : n = 2*k+1`, `hsmall : n < 9`, `hn : 1 < n` ⇒ `n ∈ {3,5,7}`.
    have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact WeakGoldbach.three_primes_three
    · exact WeakGoldbach.three_primes_five
    · exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  rcases Nat.lt_or_ge n (10 ^ 27) with hlt27 | hge27
  · have hlo : 7 ≤ n := by omega
    have hhi : n ≤ 8875694145621773516800000000000 := by
      have : (10 ^ 27 : ℕ) ≤ 8875694145621773516800000000000 := by norm_num
      omega
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      WeakGoldbach.verified_three_primes_to_8875e30 n hlo hhi hodd
    exact key p q r hp hq hr (by omega)
  obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
    WeakGoldbach.three_odd_primes_ge_10pow27 n hge27 hodd
  exact key p q r hp hq hr (by omega)
