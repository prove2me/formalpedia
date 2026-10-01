-- Prove2me | solution 2 for Richstein2001.even_goldbach_up_to_4e14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T15:23:59.387849+00:00
-- url     : https://prove2.me/submissions/d2084db4-33e7-40cb-a407-6d7e2f10259c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldbachSieve
import Theorems.Thm_TaoFivePrimes_even_goldbach_block_assembly
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses
import Theorems.Thm_TaoFivePrimes_goldbach_sieve_witness_to_primes

open Richstein2001

theorem solution (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hcov : ∀ b : ℕ, b < 400000001 →
      ∀ m : ℕ, max 4 (b * 1000000) ≤ m → m ≤ min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) →
        Even m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m := by
    intro b hb m h1 h2 hem
    have hmem : m ∈ ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter
          (fun t => Even t)) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, hem⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := segmented_sieve_block_witnesses b hb m hmem
    obtain ⟨hpi, hp'⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqmem, hcard0⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqmemLo, hqmemHi⟩ := Finset.mem_Icc.1 hqmem
    have hp5569 : p ≤ 5569 := by
      exact Finset.mem_Icc.mp hpi |>.2
    have hq2 : 2 ≤ q := by
      exact le_trans (Nat.le_max_left _ _) hqmemLo
    have hqN : q ≤ 4 * 10 ^ 14 :=
      le_trans hqmemHi (Nat.min_le_left _ _)
    have hsurv : ∀ r : ℕ, r.Prime → r ≤ 20000000 → r ∣ q → r = q := by
      intro r hr hrle hrd
      by_contra hne
      have hr2 : 2 ≤ r := hr.two_le
      have hcardne :
          {r ∈ (Finset.Icc 2 20000000).filter Nat.Prime | r ∣ q ∧ r ≠ q}.card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.2 ⟨hr2, hrle⟩, hr⟩, hrd, hne⟩⟩
      exact hcardne hcard0
    obtain ⟨p', q', hpP, hqP, hpq''⟩ :=
      TaoFivePrimes.goldbach_sieve_witness_to_primes m p q hp' hp5569 hpq.symm hq2 hqN hsurv
    exact ⟨p', q', hpP, hqP, by simpa using hpq''⟩
  exact TaoFivePrimes.even_goldbach_block_assembly hcov n h4 hN he
