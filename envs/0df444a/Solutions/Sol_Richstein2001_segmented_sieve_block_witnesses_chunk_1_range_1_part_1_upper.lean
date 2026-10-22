-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:37:11.634527+00:00
-- url     : https://prove2.me/submissions/ba141c9e-d740-46e5-bf8a-2abb7d410468
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp02
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp03
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp04
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp05
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp06
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp07
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp08
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp09
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp10
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp11
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp12
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp13
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp14
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp15
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp16
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp17
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp18
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp19
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp20

/-! Reduction of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper`
(blocks [50010000, 51000000)) to 20 groups of width 49500. A balanced case split on `b`
selects the group. -/

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : 50010000 <= b) (hhi : b < 51000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  rcases Nat.lt_or_ge b 50505000 with h | h
  ·
    rcases Nat.lt_or_ge b 50257500 with h | h
    ·
      rcases Nat.lt_or_ge b 50158500 with h | h
      ·
        rcases Nat.lt_or_ge b 50109000 with h | h
        ·
          rcases Nat.lt_or_ge b 50059500 with h | h
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01 b hb (by omega) (by omega)
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp02 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp03 b hb (by omega) (by omega)
      ·
        rcases Nat.lt_or_ge b 50208000 with h | h
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp04 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp05 b hb (by omega) (by omega)
    ·
      rcases Nat.lt_or_ge b 50406000 with h | h
      ·
        rcases Nat.lt_or_ge b 50356500 with h | h
        ·
          rcases Nat.lt_or_ge b 50307000 with h | h
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp06 b hb (by omega) (by omega)
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp07 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp08 b hb (by omega) (by omega)
      ·
        rcases Nat.lt_or_ge b 50455500 with h | h
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp09 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp10 b hb (by omega) (by omega)
  ·
    rcases Nat.lt_or_ge b 50752500 with h | h
    ·
      rcases Nat.lt_or_ge b 50653500 with h | h
      ·
        rcases Nat.lt_or_ge b 50604000 with h | h
        ·
          rcases Nat.lt_or_ge b 50554500 with h | h
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp11 b hb (by omega) (by omega)
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp12 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp13 b hb (by omega) (by omega)
      ·
        rcases Nat.lt_or_ge b 50703000 with h | h
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp14 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp15 b hb (by omega) (by omega)
    ·
      rcases Nat.lt_or_ge b 50901000 with h | h
      ·
        rcases Nat.lt_or_ge b 50851500 with h | h
        ·
          rcases Nat.lt_or_ge b 50802000 with h | h
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp16 b hb (by omega) (by omega)
          ·
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp17 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp18 b hb (by omega) (by omega)
      ·
        rcases Nat.lt_or_ge b 50950500 with h | h
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp19 b hb (by omega) (by omega)
        ·
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp20 b hb (by omega) (by omega)
