-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:22:29.845151+00:00
-- url     : https://prove2.me/submissions/cdea93ac-1828-43b8-882b-3f75c6765700
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_4

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 130000000 ≤ b) (hhi : b < 140000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hnEven := (Finset.mem_filter.mp hn).2
  have hnlo' : 130000000000000 ≤ n := by
    have h := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hnhi' : n < 140000000000000 := by
    have h := (Finset.mem_Icc.mp hnIcc).2
    omega
  obtain ⟨p, hp, q, hq, hsum⟩ :=
    Richstein2001.segmented_sieve_interval_witness_chunk_2_part_4 n hnlo' hnhi' hnEven
  refine ⟨p, hp, q, ?_, hsum⟩
  change q ∈ ((Finset.Icc (max 2 (b * 1000000 - 5569))
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter fun q =>
      (((Finset.Icc 2 20000000).filter Nat.Prime).filter
        fun r => r ∣ q ∧ r ≠ q).card = 0)
  change q ∈ ((Finset.Icc (max 2 (130000000000000 - 5569))
    140000000000000).filter fun q =>
      (((Finset.Icc 2 20000000).filter Nat.Prime).filter
        fun r => r ∣ q ∧ r ≠ q).card = 0) at hq
  rw [Finset.mem_filter] at hq ⊢
  refine ⟨Finset.mem_Icc.mpr ?_, hq.2⟩
  have hnBounds := Finset.mem_Icc.mp hnIcc
  have hpBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  constructor
  · have hblockLo : b * 1000000 ≤ n := by omega
    omega
  · have hpLower : 2 ≤ p := hpBounds.1
    omega
