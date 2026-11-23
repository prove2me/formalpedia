-- Prove2me | solution 1 for VerifiedHAMT.valid_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:24.014473+00:00
-- url     : https://prove2.me/submissions/87b8ed21-67f1-447a-b886-cee99b0c65e4

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertNode_wf_mem
public import Theorems.Thm_VerifiedHAMT_root_offset_bound


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) (value : β) :
    Valid (insert map key value) := by
  simpa [Valid, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key value).1
end VerifiedHAMT
