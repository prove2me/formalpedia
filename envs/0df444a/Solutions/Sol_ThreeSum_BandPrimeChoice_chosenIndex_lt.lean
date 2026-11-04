-- Prove2me | solution 1 for ThreeSum.BandPrimeChoice.chosenIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:38.761663+00:00
-- url     : https://prove2.me/submissions/55cc3cea-54bc-4d79-921e-9372433127a6

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightMinimum_least_lt


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
namespace ThreeSum.BandPrimeChoice
theorem _root_.solution (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := LightMinimum.least_lt _ hs
end ThreeSum.BandPrimeChoice
