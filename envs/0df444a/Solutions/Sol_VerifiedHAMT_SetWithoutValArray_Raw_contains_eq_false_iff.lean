-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:22.773789+00:00
-- url     : https://prove2.me/submissions/5b4562df-5cd9-40c5-ad70-385172c94052

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains map key = false ↔ ¬ Mem key map := by
  rw [← contains_eq_true_iff map wf key]
  cases contains map key <;> simp
end VerifiedHAMT.SetWithoutValArray.Raw
