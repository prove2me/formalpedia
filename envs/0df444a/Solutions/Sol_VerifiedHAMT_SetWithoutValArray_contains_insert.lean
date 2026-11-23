-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.contains_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:18.575808+00:00
-- url     : https://prove2.me/submissions/a1caa590-2fda-48b3-bf67-ded47b0dab7d

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) :=
  Raw.contains_insert set.toRaw set.valid key q
end VerifiedHAMT.SetWithoutValArray
