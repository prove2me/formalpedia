-- Prove2me | solution 1 for VerifiedHAMT.unique_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:18.766241+00:00
-- url     : https://prove2.me/submissions/ab1d39b8-e76c-4508-b15d-425195dd30e5

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
    (key : α) (value : β) : Unique (insert map key value).root := by
  simpa [insert] using
    (insertNode_unique_updated (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) hu key value).1
end VerifiedHAMT
