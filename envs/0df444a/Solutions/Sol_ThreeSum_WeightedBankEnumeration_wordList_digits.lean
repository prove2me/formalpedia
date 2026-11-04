-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.wordList_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:17.377992+00:00
-- url     : https://prove2.me/submissions/3d8b6ef0-be9a-4b85-90e6-c61b663f4b4c

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
theorem _root_.solution {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact (w i).isLt
end ThreeSum.WeightedBankEnumeration
