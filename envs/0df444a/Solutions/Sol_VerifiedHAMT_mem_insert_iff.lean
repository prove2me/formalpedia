-- Prove2me | solution 1 for VerifiedHAMT.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:19.198458+00:00
-- url     : https://prove2.me/submissions/2d35823c-64f8-4f9b-bc55-3104cf27ed9c

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
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key q : α) (value : β) :
    Mem q (insert map key value) ↔ q = key ∨ Mem q map := by
  simpa [Mem, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key value).2 q
end VerifiedHAMT
