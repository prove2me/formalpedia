-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.containsNode_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:22.667961+00:00
-- url     : https://prove2.me/submissions/174cc1e4-60f4-4003-b597-96db3c6ba1fe

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_sound
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_containsNode_complete

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α) :
    containsNode node (hashAt key) key = true ↔ HasKey key node :=
  ⟨containsNode_sound node (hashAt key) key, containsNode_complete wf key⟩
end VerifiedHAMT.SetWithoutValArray.Raw
