-- Prove2me | solution 1 for VerifiedHAMT.insertCollision_size_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:47.695077+00:00
-- url     : https://prove2.me/submissions/d68ad44e-0000-4bd2-867e-fe641be95b78

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Theorems.Thm_VerifiedHAMT_insertCollisionAux_size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] (keys : Array α) (vals : Array β)
    (hsz : keys.size = vals.size) (key : α) (value : β) :
    (getCollisionNodeSize (insertCollision keys vals hsz key value) == keys.size) = keys.contains key := by
  rw [insertCollision, insertCollisionAux_size]
  simp only [Array.drop_eq_extract, Array.extract_size]
  cases keys.contains key <;> simp
end VerifiedHAMT
