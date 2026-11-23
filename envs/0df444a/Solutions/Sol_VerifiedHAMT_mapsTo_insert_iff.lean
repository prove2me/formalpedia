-- Prove2me | solution 1 for VerifiedHAMT.mapsTo_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:14.687741+00:00
-- url     : https://prove2.me/submissions/b7647e69-43c7-4b85-b018-28f914301342

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertNode_unique_updated
public import Theorems.Thm_VerifiedHAMT_root_offset_bound


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) :
    MapsTo q w (insert map key value) ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ MapsTo q w map) := by
  simpa [MapsTo, insert] using
    (insertNode_unique_updated (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) hu key value).2 q w
end VerifiedHAMT
