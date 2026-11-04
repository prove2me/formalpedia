-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.codes_length_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:53.571721+00:00
-- url     : https://prove2.me/submissions/8a99744b-d118-4366-ac3f-0f83dc5d0d4a

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_gibbs


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (codes N T).length * y ^ T ≤ (1 + y + y ^ 2) ^ N := by
  rw [codes_length_eq_bank_card]
  exact bank_card_gibbs N T y hy hy1
end ThreeSum.TernaryBankEnumeration
