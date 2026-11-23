-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.nodup_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:39.226222+00:00
-- url     : https://prove2.me/submissions/945ad84f-8090-4762-a7cc-523487b7e969

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_nodup_keyList


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution (set : SetWithoutValArray α) : set.toList.Nodup :=
  Raw.nodup_keyList set.valid set.unique
end VerifiedHAMT.SetWithoutValArray
