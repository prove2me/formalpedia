-- Prove2me | solution 1 for ThreeSum.WeightedGlobalRepeatedWords.canonical_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:58.618802+00:00
-- url     : https://prove2.me/submissions/e4399141-b1ae-4b77-8691-814db29f05ca

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Theorems.Thm_ThreeSum_WeightedGlobalRepeatedWords_canonical_typed
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_eq_power_two


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatedWords
open TernaryJointType Finset
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalRepeatedWords
theorem _root_.solution {r L : ℕ} (blocks : Fin r → TritWord L) (π : DigitType)
    (h : ∀ i, HasType (blocks i) π) :
    TernaryConvolution.factorial (canonical blocks)=(2 : ℤ)^(r*π 2) := by
  rw [TernaryConvolution.factorial_eq_power_two,canonical_typed blocks π h 2]
end ThreeSum.WeightedGlobalRepeatedWords
