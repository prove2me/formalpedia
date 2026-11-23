-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.length_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:43.861515+00:00
-- url     : https://prove2.me/submissions/80d30f73-ad13-40d9-b373-eb9795cbd9a9

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Operations

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.SetWithoutValArray
theorem _root_.solution (set : SetWithoutValArray α) : set.toList.length = set.size :=
  set.size_eq.symm
end VerifiedHAMT.SetWithoutValArray
