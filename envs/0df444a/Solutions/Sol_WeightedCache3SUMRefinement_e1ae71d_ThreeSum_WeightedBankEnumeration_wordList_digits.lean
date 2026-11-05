-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.wordList_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:26.217751+00:00
-- url     : https://prove2.me/submissions/2cc3c5b5-f291-46de-9a31-e9b016d042be

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
theorem _root_.solution {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact (w i).isLt
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
