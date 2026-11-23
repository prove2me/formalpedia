-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.mem_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:56.549115+00:00
-- url     : https://prove2.me/submissions/553122e6-1b56-42d1-847a-5a5c8021a71c

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNode_wf_mem
public import Theorems.Thm_VerifiedHAMT_root_offset_bound


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Raw α) (wf : Valid map) (key q : α) :
    Mem q (insert map key) ↔ q = key ∨ Mem q map := by
  simpa [Mem, insert] using
    (insertNode_wf_mem (maxDepth.toNat - 1) 0 root_offset_bound map.root
      (by simpa [Valid] using wf) key).2 q
end VerifiedHAMT.SetWithoutValArray.Raw
