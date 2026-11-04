-- Prove2me | solution 1 for ThreeSum.WeightedScore.remaining_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:13.047834+00:00
-- url     : https://prove2.me/submissions/5dd68966-812e-4c89-90ee-735656708165

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Theorems.Thm_ThreeSum_WeightedScore_corrections_succ

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c (i+1) =
      remaining primes s q nA nB nC a b c i -
        count (joint q (primes i)) nA nB nC a b c := by
  unfold remaining
  rw [corrections_succ, Nat.sub_add_eq]
end ThreeSum.WeightedScore
