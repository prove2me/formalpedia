-- Prove2me | solution 1 for WeakGoldbach.verified_two_odd_primes_to_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T14:56:49.153254+00:00
-- url     : https://prove2.me/submissions/4274f3fa-e8c8-48c1-9523-c568e30c034e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_verified_two_primes_to_4e18

-- Reduction of `WeakGoldbach.verified_two_odd_primes_to_4e18` onto the plain
-- verified binary Goldbach range `WeakGoldbach.verified_two_primes_to_4e18`.
--
-- The two statements differ only by the added `Odd p` and `Odd q` conjuncts.
-- Since `m` is even and `m = p + q`, the summands share a parity: Mathlib's
-- `Nat.even_add'` states `Even (p + q) ↔ (Odd p ↔ Odd q)`.  So they are both
-- odd, which is the goal, or both even, which for primes forces
-- `p = q = 2` and hence `m = 4`, contradicting `6 <= m`.

open WeakGoldbach

theorem solution (m : ℕ) (h6 : 6 ≤ m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ m = p + q := by
  -- The supplier needs `4 <= m`; `m >= 6` already gives it.
  have h4 : 4 ≤ m := by omega
  obtain ⟨p, q, hp, hq, hsum⟩ :=
    WeakGoldbach.verified_two_primes_to_4e18 m h4 hB he
  -- `Nat.even_add' : Even (p + q) ↔ (Odd p ↔ Odd q)`, read off `Even m`.
  have hpiff : Odd p ↔ Odd q := by
    have h : Even (p + q) := by rw [← hsum]; exact he
    exact Nat.even_add'.mp h
  have hodd : Odd p := by
    by_contra hn
    have hpe : Even p := Nat.not_odd_iff_even.mp hn
    have hqe : Even q := Nat.not_odd_iff_even.mp ((not_congr hpiff).mp hn)
    have hp2 : p = 2 := hp.even_iff.mp hpe
    have hq2 : q = 2 := hq.even_iff.mp hqe
    omega
  exact ⟨p, q, hp, hq, hodd, hpiff.mp hodd, hsum⟩
