-- Prove2me | solution 3 for WeakGoldbach.verified_two_primes_to_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:58:22.11309+00:00
-- url     : https://prove2.me/submissions/a0141da3-6e36-4508-8933-5fa8f493c91c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Richstein2001_even_goldbach_up_to_4e14
import Theorems.Thm_WeakGoldbach_verified_two_primes_4e14_to_4e18

theorem solution (m : ℕ) (h4 : 4 ≤ m) (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  rcases Nat.le_total m (4 * 10 ^ 14) with hsmall | hbig
  · -- `m <= 4 * 10^14` is exactly the Richstein hypothesis. Its conclusion
    -- is oriented `p + q = m`, so it is re-oriented to the parent's `m = p + q`.
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      Richstein2001.even_goldbach_up_to_4e14 m h4 hsmall he
    exact ⟨p, q, hp, hq, hpq.symm⟩
  · -- `4 * 10^14 ≤ m ≤ 4 * 10^18` is the extended verified window. Its
    -- hypothesis is the *strict* `4 * 10^14 < m`, so `hbig` is not enough on
    -- its own: the shared endpoint `m = 4 * 10^14` has to be sent to the
    -- Richstein branch instead, which is why the split below is a trichotomy
    -- rather than a two-way `le_total`.
    rcases Nat.eq_or_lt_of_le hbig with heq | hlt
    · -- The endpoint `m = 4 * 10^14` is covered by Richstein's range.
      obtain ⟨p, q, hp, hq, hpq⟩ :=
        Richstein2001.even_goldbach_up_to_4e14 m h4 (by omega) he
      exact ⟨p, q, hp, hq, hpq.symm⟩
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      WeakGoldbach.verified_two_primes_4e14_to_4e18 m hlt hB he
    exact ⟨p, q, hp, hq, hpq⟩
