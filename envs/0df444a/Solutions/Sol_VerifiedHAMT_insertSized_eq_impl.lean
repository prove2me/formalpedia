-- Prove2me | solution 1 for VerifiedHAMT.insertSized_eq_impl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:06.438254+00:00
-- url     : https://prove2.me/submissions/e7c10b84-5f10-4274-ad6d-0240ef461203

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Theorems.Thm_VerifiedHAMT_insertCollision_size_eq
public import Theorems.Thm_VerifiedHAMT_insertSizedRaw_eq
attribute [local simp] VerifiedHAMT.insertCollision_size_eq

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution : @insertSized = @insertSizedImpl := by
  funext α β _ _ s key value
  simp only [insertSized, insertSizedImpl, insertSizedRaw_eq, insert]
end VerifiedHAMT
