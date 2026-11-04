-- Prove2me | solution 1 for ThreeSum.WeightedGlobalRepeatedWords.canonical_typed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:46.070852+00:00
-- url     : https://prove2.me/submissions/a5cbf675-3950-4228-9109-93e04973975b

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_typed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalRepeatedWords
theorem _root_.solution {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) : HasType (canonical blocks) (fun d => r*π d) :=
  typed _ π (fun i => h i.rev)
end ThreeSum.WeightedGlobalRepeatedWords
