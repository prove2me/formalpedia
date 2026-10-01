-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:45:03.996666+00:00
-- url     : https://prove2.me/submissions/8e9ae522-8d2f-43e3-959f-b1179a984a01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5

theorem solution (b : Nat) (hb : Nat.lt b 400000001)
    (hlo : Nat.le 250000000 b) (hhi : Nat.lt b 300000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by
  intro n hn
  by_cases h1 : Nat.lt b 260000000
  case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1 b hb hlo h1 n hn
  case neg =>
    by_cases h2 : Nat.lt b 270000000
    case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_2 b hb (Nat.not_lt.mp h1) h2 n hn
    case neg =>
      by_cases h3 : Nat.lt b 280000000
      case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_3 b hb (Nat.not_lt.mp h2) h3 n hn
      case neg =>
        by_cases h4 : Nat.lt b 290000000
        case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_4 b hb (Nat.not_lt.mp h3) h4 n hn
        case neg => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5 b hb (Nat.not_lt.mp h4) hhi n hn