-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertSized_eq_impl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:28.997804+00:00
-- url     : https://prove2.me/submissions/0f70abef-d6c8-420c-b484-00bdf8300f1f

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertSizedRaw_eq
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution : @insertSized = @insertSizedImpl := by
  funext α _ _ s key
  simp only [insertSized, insertSizedImpl, insertSizedRaw_eq, insert]
end VerifiedHAMT.SetWithoutValArray.Raw
