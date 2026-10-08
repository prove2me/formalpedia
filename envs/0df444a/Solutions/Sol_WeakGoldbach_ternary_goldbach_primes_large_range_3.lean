-- Prove2me | solution 3 for WeakGoldbach.ternary_goldbach_primes_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:17:48.874465+00:00
-- url     : https://prove2.me/submissions/a26b7446-fd5c-41bc-a98c-6a4b469eef43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_large_range

set_option autoImplicit false

theorem solution (n : ℕ) (hodd : Odd n) (hlo : Real.exp 3100 ≤ (n : ℝ)) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      2 < p ∧ 2 < q ∧ 2 < r ∧ n = p + q + r := by
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_large_range n hodd hlo
  refine ⟨p, q, r, hp, hq, hr, ?_, ?_, ?_, hsum⟩
  · exact lt_of_lt_of_le (by norm_num : 2 < 3) (hp.odd_iff.mp hop)
  · exact lt_of_lt_of_le (by norm_num : 2 < 3) (hq.odd_iff.mp hoq)
  · exact lt_of_lt_of_le (by norm_num : 2 < 3) (hr.odd_iff.mp hor)

#print axioms solution
