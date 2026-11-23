-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:14.636721+00:00
-- url     : https://prove2.me/submissions/02794155-edf6-4a04-a7e6-a0022eea24a6

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_wf_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_collisionNode
public import Theorems.Thm_VerifiedHAMT_wellFormed_collisionNode


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α) :
    letI res := insertNoExpand node (hashAt key) key
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction wf generalizing key with
  | collision hashAt keys =>
    rw [insertNoExpand.eq_def]
    exact ⟨wellFormed_collisionNode _ _, fun q => insertCollisionAux_mem keys 0 key q⟩
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_wf_mem hashAt es _ key (.entries hs route children)
    grind [Array.mem_iff_getElem]
end VerifiedHAMT.SetWithoutValArray.Raw
