-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertCollision_size_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:48:58.558076+00:00
-- url     : https://prove2.me/submissions/c620f5b6-8d8f-4e22-9398-96eeeae0bc0e

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] (keys : Array α) (key : α) :
    (getCollisionNodeSize (insertCollision keys key) == keys.size) = keys.contains key := by
  rw [insertCollision, insertCollisionAux_size]
  simp only [Array.drop_eq_extract, Array.extract_size]
  cases keys.contains key <;> simp
end VerifiedHAMT.SetWithoutValArray.Raw
