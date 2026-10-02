-- Prove2me | solution 4 for Richstein2001.even_goldbach_up_to_4e14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T01:42:41.378414+00:00
-- url     : https://prove2.me/submissions/a2f6ef76-3fb1-45a8-888e-552cab2ddb87
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
  -- `survivors` says no sieving prime other than q itself divides q, so the
  -- corresponding finset is empty. `Finset.card_eq_zero.mp` turns the card
  -- zero into that literal emptiness.
  have hcard0 : ((Finset.Icc 2 20000000).filter Nat.Prime).filter
      (fun r => r ∣ q ∧ r ≠ q) = ∅ := Finset.card_eq_zero.mp hcard
  -- Repair of candidate 5964. Two changes, both from the compiler evidence.
  --
  -- (1) Supplier. `TaoFivePrimes.goldbach_survivor_prime_2e7` (Proved,
  -- 8d527ece) takes the NEGATIVE form `∀ p, p.Prime → p ≤ 20000000 →
  -- ¬ p ∣ n`. That hypothesis is not derivable from the certificate: take
  -- r = q, and q ∣ q holds, so `¬ q ∣ q` is false. That is exactly the cause of
  -- the stranded `⊢ ¬ r = q` in 5964: the writer reached for a side goal that
  -- is unsatisfiable. The certificate yields the POSITIVE form instead, and
  -- `TaoFivePrimes.goldbach_sieve_witness_to_primes` (Proved, 2f0e5d5c) takes
  -- exactly that positive form and concludes a genuine Goldbach partition
  -- directly, so this supplier both accepts the hypothesis and closes the goal.
  --
  -- (2) Frame. The goal `∀ r, r.Prime → r ≤ 20000000 → r ∣ q → r = q` is
  -- satisfiable, so it is proved by splitting on `r = q` rather than by
  -- contradiction:
  --   * `r = q`  — the goal is already the hypothesis, so it closes;
  --   * `r ≠ q`  — `r` is then a member of the finset `hcard0` shows empty,
  --     giving `False`.
  exact TaoFivePrimes.goldbach_sieve_witness_to_primes n p q hpPrime hp5569
    hpq.symm hq2 hqN (by
      intro r hr hrle hd
      by_cases heq : r = q
      · exact heq
      · exfalso
        have hrprim : r ∈ (Finset.Icc 2 20000000).filter Nat.Prime :=
          Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.Prime.two_le hr, hrle⟩, hr⟩
        have hmem : r ∈ ((Finset.Icc 2 20000000).filter Nat.Prime).filter
            (fun r => r ∣ q ∧ r ≠ q) :=
          Finset.mem_filter.mpr ⟨hrprim, hd, heq⟩
        rw [hcard0] at hmem
        exact (Finset.notMem_empty r) hmem)
