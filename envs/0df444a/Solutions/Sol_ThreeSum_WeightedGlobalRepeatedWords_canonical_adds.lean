-- Prove2me | solution 1 for ThreeSum.WeightedGlobalRepeatedWords.canonical_adds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:46.231506+00:00
-- url     : https://prove2.me/submissions/ea77b9c9-f97e-4e2a-9180-604aeae2b3ba

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_adds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalRepeatedWords
theorem _root_.solution {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) :
    PointwiseSum (canonical a) (canonical b) (canonical q) :=
  adds _ _ _ (fun i => h i.rev)
end ThreeSum.WeightedGlobalRepeatedWords
