-- Prove2me | solution 1 for ThreeSum.WeightedScore.next_count_le_remaining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:11.432012+00:00
-- url     : https://prove2.me/submissions/229d4502-4c75-4516-9c17-f2e510461bd2

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_WeightedScore_corrections_succ
import Theorems.Thm_ThreeSum_WeightedScore_corrections_le

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    count (joint q (primes i)) nA nB nC a b c ≤
      remaining primes s q nA nB nC a b c i := by
  have h := (corrections_le primes q nA nB nC a b c (i+1)).trans
    (Nat.mul_le_mul_right (count q nA nB nC a b c) (by omega : i+1 ≤ s))
  rw [corrections_succ] at h
  unfold remaining
  omega
end ThreeSum.WeightedScore
