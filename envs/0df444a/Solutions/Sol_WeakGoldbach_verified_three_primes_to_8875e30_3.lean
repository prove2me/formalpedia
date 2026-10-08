-- Prove2me | solution 3 for WeakGoldbach.verified_three_primes_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:57:56.994829+00:00
-- url     : https://prove2.me/submissions/e8f8448c-b709-4db3-96f1-c1516f7ad07f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30

set_option autoImplicit false

/-- Odd primes are primes; the only verified-range gap is `n = 7`, where `2 + 2 + 3` works. -/
theorem solution (n : ℕ) (hlo : 7 ≤ n) (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  by_cases hn7 : n = 7
  · subst hn7
    refine ⟨2, 2, 3, Nat.prime_two, Nat.prime_two, Nat.prime_three, by norm_num⟩
  · have h9 : 9 ≤ n := by
      have hnlt : 7 < n := Nat.lt_of_le_of_ne hlo (Ne.symm hn7)
      rcases Nat.lt_or_ge n 9 with h | h
      · rcases hodd with ⟨k, rfl⟩
        omega
      · exact h
    obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.verified_three_odd_primes_to_8875e30 n h9 hhi hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩

#print axioms solution
