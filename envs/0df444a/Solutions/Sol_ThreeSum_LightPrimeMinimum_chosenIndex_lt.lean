-- Prove2me | solution 1 for ThreeSum.LightPrimeMinimum.chosenIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:47.623067+00:00
-- url     : https://prove2.me/submissions/1182b1a5-fa0c-470b-a089-3382dfa421fd

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Theorems.Thm_ThreeSum_LightMinimum_least_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimeMinimum
theorem _root_.solution (primes : ℕ → ℕ) {s q nA nB nC : ℕ}
    (A B C : ℕ → ℤ) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC A B C < s :=
  LightMinimum.least_lt _ hs
end ThreeSum.LightPrimeMinimum
