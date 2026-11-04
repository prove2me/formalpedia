-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.wordList_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:49.006327+00:00
-- url     : https://prove2.me/submissions/0d3ba4e9-bd30-49d6-950b-bf6eb6b56ee9

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact (w i).isLt
end ThreeSum.TernaryBankEnumeration
