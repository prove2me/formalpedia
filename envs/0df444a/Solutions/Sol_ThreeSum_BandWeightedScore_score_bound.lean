-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.score_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:49.756614+00:00
-- url     : https://prove2.me/submissions/5bc310d3-e518-4dd5-ae1d-444821890fa4

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_ThreeSum_BandWeightedScore_partialScore_bound

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj
end ThreeSum.BandWeightedScore
