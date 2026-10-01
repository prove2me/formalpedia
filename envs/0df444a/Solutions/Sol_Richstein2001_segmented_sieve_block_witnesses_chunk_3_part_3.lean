-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:24:48.163074+00:00
-- url     : https://prove2.me/submissions/d2dd9aa3-a8ce-4b13-8570-ef26c57801f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_3_interval_witness

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 170000000 ≤ b) (hhi : b < 180000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnI, hnEven⟩
  rcases Finset.mem_Icc.mp hnI with ⟨hnlo, hnhi⟩
  have hnBlockLo : 170000000000000 ≤ n := by
    have hbLo : 170000000 * 1000000 ≤ b * 1000000 := by
      exact Nat.mul_le_mul_right 1000000 hlo
    have hnBase : b * 1000000 ≤ n := le_trans (le_max_right _ _) hnlo
    omega
  have hnBlockHi : n < 180000000000000 := by
    have hbPlus : b + 1 ≤ 180000000 := by omega
    have hbUpper : (b + 1) * 1000000 ≤ 180000000000000 := by
      exact Nat.mul_le_mul_right 1000000 hbPlus
    have hnUpper : n ≤ (b + 1) * 1000000 - 1 :=
      le_trans hnhi (min_le_right _ _)
    omega
  obtain ⟨p, q, hpPrime, hpBound, hsum, hno⟩ :=
    Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_3_interval_witness
      n hnBlockLo hnBlockHi hnEven
  have hpMem : p ∈ ((Finset.Icc 2 5569).filter Nat.Prime) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      exact ⟨hpPrime.two_le, hpBound⟩
    · exact hpPrime
  refine ⟨p, hpMem, q, ?_, hsum⟩
  change q ∈ ((Finset.Icc (max 2 (b * 1000000 - 5569))
    (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter fun q =>
      (((Finset.Icc 2 20000000).filter Nat.Prime).filter
        fun r => r ∣ q ∧ r ≠ q).card = 0)
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_Icc]
    constructor
    · have hnBase : b * 1000000 ≤ n := le_trans (le_max_right _ _) hnlo
      omega
    · have hqN : q ≤ n := by omega
      exact le_trans hqN hnhi
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
