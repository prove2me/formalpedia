-- Prove2me | solution 1 for Richstein2001.segmented_sieve_block_witnesses
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:32:32.491421+00:00
-- url     : https://prove2.me/submissions/db43bda3-a1b6-4718-be84-335ea43f157e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7
import Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_final_block

theorem solution (b : ℕ) (hb : b < 400000001) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  classical
  intro n hn
  by_cases h0 : b < 50000000
  case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_0 b hb (by omega) h0 n hn
  case neg =>
    by_cases h1 : b < 100000000
    case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_1 b hb (by omega) h1 n hn
    case neg =>
      by_cases h2 : b < 150000000
      case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_2 b hb (by omega) h2 n hn
      case neg =>
        by_cases h3 : b < 200000000
        case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_3 b hb (by omega) h3 n hn
        case neg =>
          by_cases h4 : b < 250000000
          case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_4 b hb (by omega) h4 n hn
          case neg =>
            by_cases h5 : b < 300000000
            case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_5 b hb (by omega) h5 n hn
            case neg =>
              by_cases h6 : b < 350000000
              case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_6 b hb (by omega) h6 n hn
              case neg =>
                by_cases h7 : b < 400000000
                case pos => exact Richstein2001.segmented_sieve_block_witnesses_chunk_7 b hb (by omega) h7 n hn
                case neg =>
                  have hfinal : b = 400000000 := by omega
                  exact Richstein2001.segmented_sieve_block_witnesses_final_block b hb hfinal n hn


