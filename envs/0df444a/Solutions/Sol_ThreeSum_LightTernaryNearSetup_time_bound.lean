-- Prove2me | solution 1 for ThreeSum.LightTernaryNearSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:35.491652+00:00
-- url     : https://prove2.me/submissions/2b3f5d45-9942-461e-aa16-90171b689253

import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_time_bank_bound
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearSetup
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) :
    time Q D≤3000*(N+1)^2*((TernaryNearEnumeration.codes (wordList Q) D).length+1) := by
  have he := LightTernaryNearEnumerationMain.time_bank_bound Q D
  rw [←TernaryNearBankEnumeration.codes_length_eq_nearWords_card Q D] at he
  unfold time LightTernaryNearDigits.time LightTernaryCodes.digitTime LightMaskErase.time powTableTime
  nlinarith only [he, Nat.zero_le (TernaryNearEnumeration.codes (wordList Q) D).length]
end ThreeSum.LightTernaryNearSetup
