-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.score_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:34.179417+00:00
-- url     : https://prove2.me/submissions/73ab9dff-4647-4874-bd52-35f955f1665c

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_ThreeSum_BandWeightedScore_block_congr

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    score primes s q nA nB nC g A B C rs=score primes s q nA nB nC g A' B' C' rs := by
  unfold score partialScore
  exact sum_congr rfl fun i _ => block_congr (rs.getD i default) hA hB hC
end ThreeSum.BandWeightedScore
