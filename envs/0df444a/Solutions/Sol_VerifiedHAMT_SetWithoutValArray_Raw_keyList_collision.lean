-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:33:57.779941+00:00
-- url     : https://prove2.me/submissions/50825976-3797-4068-afad-0ea724cd0f8a

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {keys : Array α} : keyList (.collision keys) = keys.toList := by
  simp [keyList]
end VerifiedHAMT.SetWithoutValArray.Raw
