-- Prove2me | solution 1 for TaoFivePrimes.even_goldbach_block_assembly
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T16:54:55.553835+00:00
-- url     : https://prove2.me/submissions/8771987a-28fc-4bda-a9da-cfe0a1248ab8

import Mathlib

set_option autoImplicit false

theorem solution
    (hcov : ∀ b : ℕ, b < 400000001 →
      ∀ n : ℕ, max 4 (b * 1000000) ≤ n → n ≤ min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) →
        Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n)
    (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  -- Locate the block: b = n / 10^6. Div bounds are linear after naming the quotient.
  have hpos : (0 : ℕ) < 1000000 := by norm_num
  have hdiv_lo : (n / 1000000) * 1000000 ≤ n := Nat.div_mul_le_self n 1000000
  -- Upper div bound from the division algorithm: n = 10^6·(n/10^6) + n%10^6.
  have hmod : n % 1000000 < 1000000 := Nat.mod_lt n hpos
  have hdiv : 1000000 * (n / 1000000) + n % 1000000 = n := Nat.div_add_mod n 1000000
  have hdiv_hi : n < (n / 1000000 + 1) * 1000000 := by omega
  -- The block index is in range: n ≤ 4·10^14 gives n/10^6 ≤ 4·10^8 < 400000001.
  have hb : n / 1000000 < 400000001 := by omega
  -- n lies in the clipped block interval.
  have hmax : max 4 ((n / 1000000) * 1000000) ≤ n := by omega
  have hmin : n ≤ min (4 * 10 ^ 14) ((n / 1000000 + 1) * 1000000 - 1) := by omega
  exact hcov (n / 1000000) hb n hmax hmin he
