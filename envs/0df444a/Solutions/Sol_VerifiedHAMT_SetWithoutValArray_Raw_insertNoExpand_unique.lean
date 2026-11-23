-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:10.270048+00:00
-- url     : https://prove2.me/submissions/d5002055-2a25-40da-b2e4-ad44e84ae1a4

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_unique

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) :
    Unique (insertNoExpand node (hashAt key) key) := by
  induction wf generalizing key with
  | collision hashAt keys =>
    rw [insertNoExpand.eq_def]
    cases hu with
    | collision distinct => exact insertCollisionAux_unique keys distinct 0 key (by omega)
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_unique hashAt es _ key (.entries hs route children) hu
    grind [Array.mem_iff_getElem]
end VerifiedHAMT.SetWithoutValArray.Raw
