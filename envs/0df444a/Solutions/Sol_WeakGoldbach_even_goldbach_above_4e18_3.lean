-- Prove2me | solution 3 for WeakGoldbach.even_goldbach_above_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:17:35.966975+00:00
-- url     : https://prove2.me/submissions/fbf8bf66-c85a-44ac-8d50-8737364a7c20
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_prime_pair_above_2e18

theorem solution (n : ℕ) (h : 4 * 10 ^ 18 < n) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  -- The child's pair `m - t` and `m + t` sums to `2 * m`, not to `m`, so the
  -- child must be instantiated at the *half* of `n`. This is exactly why the
  -- parent threshold is `4 * 10^18`: it is twice the child's `2 * 10^18`.
  -- `Even n` is what supplies that half: `Even n` unfolds to `2 ∣ n`, which
  -- is a `Nat` divisibility, and that gives `n = 2 * m` for a natural `m`.
  obtain ⟨m, hm⟩ := (even_iff_two_dvd).mp he
  have hlt : 2 * 10 ^ 18 < m := by omega
  obtain ⟨t, ht, hp, hq⟩ := WeakGoldbach.symmetric_prime_pair_above_2e18 m hlt
  refine ⟨m - t, m + t, hp, hq, ?_⟩
  -- `Nat.sub_le` is deliberately not named here: the trivial bound `m - 2 ≤ m`
  -- is a decision-procedure fact, so `omega` discharges it inside the final
  -- step rather than through a hand-picked lemma name.
  have hmt : t ≤ m := by omega
  omega
