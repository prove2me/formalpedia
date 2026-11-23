-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.contains_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:35.635177+00:00
-- url     : https://prove2.me/submissions/612a2950-d01a-43dd-8ea6-c9285b207832

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map :=
  containsNode_eq_true_iff wf key
end VerifiedHAMT.SetWithoutValArray.Raw
