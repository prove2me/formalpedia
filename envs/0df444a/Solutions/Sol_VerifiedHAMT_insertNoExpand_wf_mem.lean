-- Prove2me | solution 1 for VerifiedHAMT.insertNoExpand_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:50.953908+00:00
-- url     : https://prove2.me/submissions/8c51ab49-1820-4a63-ad1f-081028594273

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertCollisionAux_mem
public import Theorems.Thm_VerifiedHAMT_insertEntries_wf_mem
public import Theorems.Thm_VerifiedHAMT_wellFormed_collisionNode


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand.eq_def]
    exact ⟨wellFormed_collisionNode _ _, fun q => insertCollisionAux_mem keys vals hsz 0 key q value⟩
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_wf_mem hashAt es _ key value (.entries hs route children)
    grind [Array.mem_iff_getElem]
end VerifiedHAMT
