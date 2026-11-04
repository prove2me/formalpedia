-- Prove2me | solution 1 for ThreeSum.TernaryNearBankEnumeration.codes_length_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:10.783336+00:00
-- url     : https://prove2.me/submissions/0dc83a3e-6812-4ba4-be79-b62344878855

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
namespace ThreeSum.TernaryNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) (z : ℝ)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (TernaryNearEnumeration.codes (wordList Q) D).length*z^D ≤
      ∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z else 1+z+z^2) := by
  rw [codes_length_eq_nearWords_card]
  exact nearWords_card_gibbs Q D z hz hz1
end ThreeSum.TernaryNearBankEnumeration
