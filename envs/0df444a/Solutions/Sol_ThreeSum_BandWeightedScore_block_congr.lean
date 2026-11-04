-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.block_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:29:43.758227+00:00
-- url     : https://prove2.me/submissions/47fe09ae-942e-4819-bad6-fd8dde8b2120

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_ThreeSum_BandWeightedScore_position_lt
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_LightPrimeMinimum_score_congr


set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    block primes s q nA nB nC g A B C r=block primes s q nA nB nC g A' B' C' r := by
  unfold block
  split_ifs
  · exact LightPrimeMinimum.score_congr
      (fun i hi => hA _ (position_lt hi)) (fun i hi => hB _ (position_lt hi))
      (fun i hi => hC _ (position_lt hi))
  · rfl
end ThreeSum.BandWeightedScore
