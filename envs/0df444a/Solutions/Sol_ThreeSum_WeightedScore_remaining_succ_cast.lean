-- Prove2me | solution 1 for ThreeSum.WeightedScore.remaining_succ_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:28.873015+00:00
-- url     : https://prove2.me/submissions/fa11df02-ece3-4c4a-83b9-c061732f7e79

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_WeightedScore_next_count_le_remaining
import Theorems.Thm_ThreeSum_WeightedScore_remaining_succ

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    (remaining primes s q nA nB nC a b c (i+1) : ℤ) =
      (remaining primes s q nA nB nC a b c i : ℤ) -
        (count (joint q (primes i)) nA nB nC a b c : ℤ) := by
  rw [remaining_succ, Nat.cast_sub (next_count_le_remaining primes a b c hi)]
end ThreeSum.WeightedScore
