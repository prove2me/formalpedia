-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:06:11.226314+00:00
-- url     : https://prove2.me/submissions/d1e82630-2c68-4ce4-82c5-31626a86227f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_5_interval_witness

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 190000000 ≤ b) (hhi : b < 200000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hnEven := (Finset.mem_filter.mp hn).2
  have hnlo : 190000000000000 ≤ n := by
    have h := (Finset.mem_Icc.mp hnIcc).1
    omega
  have hnhi : n < 200000000000000 := by
    have h := (Finset.mem_Icc.mp hnIcc).2
    omega
  obtain ⟨p, q, hpPrime, hpLe, hsum, hno⟩ :=
    Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_5_interval_witness
      n hnlo hnhi hnEven
  have hpMem : p ∈ ((Finset.Icc 2 5569).filter Nat.Prime) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      exact ⟨hpPrime.two_le, hpLe⟩
    · exact hpPrime
  have hpLeBound : p ≤ 5569 := hpLe
  refine ⟨p, hpMem, q, ?_, hsum⟩
  change q ∈ ((Finset.Icc (max 2 (b * 1000000 - 5569))
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter fun q =>
      (((Finset.Icc 2 20000000).filter Nat.Prime).filter
        fun r => r ∣ q ∧ r ≠ q).card = 0)
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_Icc]
    constructor
    · have hbM : b * 1000000 ≤ n := by
        have hn' := (Finset.mem_Icc.mp hnIcc).1
        omega
      have hsplit : b * 1000000 ≤ p + q := by omega
      have hqLower : b * 1000000 - 5569 ≤ q := by omega
      exact max_le_iff.mpr ⟨by omega, hqLower⟩
    · have hnIcc' := Finset.mem_Icc.mp hnIcc
      omega
  · have hempty :
        ((Finset.Icc 2 20000000).filter Nat.Prime).filter
          (fun r => r ∣ q ∧ r ≠ q) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr hdiv
      have hrMem := Finset.mem_filter.mp hr
      have hrBound := (Finset.mem_Icc.mp hrMem.1).2
      exact hdiv.2 (hno r hrMem.2 hrBound hdiv.1)
    rw [hempty]
    simp
