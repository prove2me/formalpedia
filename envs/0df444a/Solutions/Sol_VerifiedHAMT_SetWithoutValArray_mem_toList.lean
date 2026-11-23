-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.mem_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:35.260168+00:00
-- url     : https://prove2.me/submissions/1b9e31b6-cf26-40bf-82f9-907904d2ef79

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_keyList


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution (set : SetWithoutValArray α) (key : α) : key ∈ set.toList ↔ key ∈ set :=
  Raw.mem_keyList set.valid key
end VerifiedHAMT.SetWithoutValArray
