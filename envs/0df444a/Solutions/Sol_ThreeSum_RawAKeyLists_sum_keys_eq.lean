-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.sum_keys_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:11.356249+00:00
-- url     : https://prove2.me/submissions/6af1c88f-2cef-40a7-a090-ce6b065924ad

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_length_records
import Theorems.Thm_ThreeSum_RawAKeyLists_key_getD_record
import Theorems.Thm_ThreeSum_GlobalKeyOffset_key_getD_record
import Theorems.Thm_ThreeSum_GlobalKeyOffset_keys_length_records


set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution (P : ℤ) (xs : List ℤ) (f : ℤ → ℕ) :
    (∑ i : Fin (keys P xs).length, f ((keys P xs).getD i.val 0))=
      ∑ i : Fin xs.length, ∑ j : Fin 3, f (xs.getD i.val 0%P+lift j*P) := by
  rw [keys_length_records]
  calc
    _ = ∑ r : Record xs, f (key P xs r) := by
      apply Fintype.sum_equiv (recordEquiv xs)
      intro i
      rw [key_getD_record]
    _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_comm]; rfl
end ThreeSum.RawAKeyLists
