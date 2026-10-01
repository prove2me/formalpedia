-- Prove2me | solution 2 for Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T22:07:25.053588+00:00
-- url     : https://prove2.me/submissions/6dc49164-3632-4f5f-9dd6-c73399a9686d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_340
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_341
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_342
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_343
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_344
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_345
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_346
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_347
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_348
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_349

theorem solution (b : Nat) (hb : b < 400000001)
    (hlo : LE.le 340000000 b) (hhi : b < 350000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by
  intro n hn
  by_cases h1 : b < 341000000
  case pos =>
    exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_340
      b hb (by omega) h1 n hn
  case neg =>
    by_cases h2 : b < 342000000
    case pos =>
      exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_341
        b hb (by omega) h2 n hn
    case neg =>
      by_cases h3 : b < 343000000
      case pos =>
        exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_342
          b hb (by omega) h3 n hn
      case neg =>
        by_cases h4 : b < 344000000
        case pos =>
          exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_343
            b hb (by omega) h4 n hn
        case neg =>
          by_cases h5 : b < 345000000
          case pos =>
            exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_344
              b hb (by omega) h5 n hn
          case neg =>
            by_cases h6 : b < 346000000
            case pos =>
              exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_345
                b hb (by omega) h6 n hn
            case neg =>
              by_cases h7 : b < 347000000
              case pos =>
                exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_346
                  b hb (by omega) h7 n hn
              case neg =>
                by_cases h8 : b < 348000000
                case pos =>
                  exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_347
                    b hb (by omega) h8 n hn
                case neg =>
                  by_cases h9 : b < 349000000
                  case pos =>
                    exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_348
                      b hb (by omega) h9 n hn
                  case neg =>
                    exact Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_349
                      b hb (by omega) hhi n hn
