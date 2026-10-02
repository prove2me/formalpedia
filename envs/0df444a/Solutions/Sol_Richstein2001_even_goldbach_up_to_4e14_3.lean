-- Prove2me | solution 3 for Richstein2001.even_goldbach_up_to_4e14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T21:39:21.056244+00:00
-- url     : https://prove2.me/submissions/bd324347-eaaa-4fa4-bc2f-b600936e1e8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses
import Theorems.Thm_TaoFivePrimes_goldbach_blocks_tile_range
import Theorems.Thm_TaoFivePrimes_goldbach_sieve_witness_to_primes

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

open Richstein2001

theorem solution (n : ℕ) (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  -- Tile [4, 4e14] by the 10^6 blocks the sieve certificate is indexed by.
  obtain ⟨b, hb, hblo, hbhi⟩ := TaoFivePrimes.goldbach_blocks_tile_range n h4 hN
  -- The block certificate gives a small prime plus a sieve survivor.
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    segmented_sieve_block_witnesses b hb n
      (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hblo, hbhi⟩, he⟩)
  obtain ⟨hpIcc, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp2, hp5569⟩ := Finset.mem_Icc.mp hpIcc
  obtain ⟨hqIcc, hcard⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqlo, hqhi⟩ := Finset.mem_Icc.mp hqIcc
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hqlo
  have hqN : q ≤ 4 * 10 ^ 14 := le_trans hqhi (min_le_left _ _)
  -- `survivors` says the sieving primes other than q itself do not divide q.
  -- `Finset.card_eq_zero.mp` turns that into the finset being literally empty.
  have hcard0 : ((Finset.Icc 2 20000000).filter Nat.Prime).filter
      (fun r => r ∣ q ∧ r ≠ q) = ∅ := Finset.card_eq_zero.mp hcard
  -- The supplier wants the *positive* form `r ∣ q -> r = q`, not `¬ r ∣ q`:
  -- the divisor is q itself, not the absence of any small divisor.
  have hsurv : ∀ r : ℕ, r.Prime → r ≤ 20000000 → r ∣ q → r = q := by
    intro r hr hrle hd
    by_contra hne
    have hrprim : r ∈ (Finset.Icc 2 20000000).filter Nat.Prime :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.Prime.two_le hr, hrle⟩, hr⟩
    have hmem : r ∈ ((Finset.Icc 2 20000000).filter Nat.Prime).filter
        (fun r => r ∣ q ∧ r ≠ q) := Finset.mem_filter.mpr ⟨hrprim, hd, hne⟩
    rw [hcard0] at hmem
    exact (Finset.notMem_empty r) hmem
  -- This supplier states `p + q = n`; the block certificate gives `n = p + q`,
  -- so it must be passed as `hpq.symm`.
  exact TaoFivePrimes.goldbach_sieve_witness_to_primes n p q
    hpPrime hp5569 hpq.symm hq2 hqN hsurv
