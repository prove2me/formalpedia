-- Prove2me | solution 1 for ThreeSum.WeightedScore.corrections_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:29.351202+00:00
-- url     : https://prove2.me/submissions/a0b259ff-6dcf-4086-a841-51a8df1299ee

import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_WeightedScore

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedScore
open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators
namespace ThreeSum.WeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c (i+1) =
      corrections primes q nA nB nC a b c i +
        count (joint q (primes i)) nA nB nC a b c := by
  exact sum_range_succ _ _
end ThreeSum.WeightedScore
