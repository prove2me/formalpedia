-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.partialScore_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:47.912185+00:00
-- url     : https://prove2.me/submissions/399e9bb0-6802-4957-802f-4fdef5d83422

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_Light_Ends_block


set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ) :
    partialScore primes s q nA nB nC g A B C rs (k+1)=
      partialScore primes s q nA nB nC g A B C rs k+
        block primes s q nA nB nC g A B C (rs.getD k default) := sum_range_succ _ _
end ThreeSum.BandWeightedScore
