-- Prove2me | solution 12 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T10:35:13.464445+00:00
-- url     : https://prove2.me/submissions/96765ff9-9f5e-4c32-8f84-30883afbd2d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_ternary_goldbach_intermediate_range
import Theorems.Thm_WeakGoldbach_ternary_goldbach_large_range

set_option maxRecDepth 10000 in
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- Variant W. Differs from V in the cause-linked part along two axes:
  --
  --  * The lower band uses `verified_three_odd_primes_to_8875e30`, which
  --    additionally returns `Odd p / Odd q / Odd r`, so the destructured oddness
  --    `hk` is consumed there and no `omega` conversion of `n = p+q+r` is needed
  --    in that branch.
  --  * The two upper bands use `ternary_goldbach_intermediate_range` /
  --    `ternary_goldbach_large_range`, which are the same-revision `all-odd`
  --    formulations, so the split at `exp 3100` is exercised again but now
  --    with the `simpa [add_assoc]` discharge that 5560 was missing.
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
  · have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact WeakGoldbach.three_primes_three
    · exact WeakGoldbach.three_primes_five
    · exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  rcases Nat.lt_or_ge n (10 ^ 27) with hlt27 | hge27
  · have hlo : 9 ≤ n := hbig
    have hhi : n ≤ 8875694145621773516800000000000 := by
      have : (10 ^ 27 : ℕ) ≤ 8875694145621773516800000000000 := by norm_num
      omega
    obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.verified_three_odd_primes_to_8875e30 n hlo hhi hodd
    exact key p q r hp hq hr (by omega)
  rcases le_or_gt (Real.exp 3100) (n : ℝ) with hle | hgt
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_large_range n hodd hle
    exact key p q r hp hq hr (by omega)
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_intermediate_range n hodd hge27 hgt
    exact key p q r hp hq hr (by omega)
