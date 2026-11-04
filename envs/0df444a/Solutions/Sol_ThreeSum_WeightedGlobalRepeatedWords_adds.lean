-- Prove2me | solution 1 for ThreeSum.WeightedGlobalRepeatedWords.adds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:06.302947+00:00
-- url     : https://prove2.me/submissions/ca81a514-e76e-45c5-8f58-d606e185f42f

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalRepeatedWords
theorem _root_.solution {r L : ℕ} (a b q : Fin r → TritWord L)
    (h : ∀ i, PointwiseSum (a i) (b i) (q i)) : PointwiseSum (word a) (word b) (word q) := by
  intro i
  exact h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
end ThreeSum.WeightedGlobalRepeatedWords
