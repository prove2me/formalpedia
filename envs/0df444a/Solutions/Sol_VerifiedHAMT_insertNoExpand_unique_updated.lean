-- Prove2me | solution 1 for VerifiedHAMT.insertNoExpand_unique_updated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:01.361814+00:00
-- url     : https://prove2.me/submissions/b21151ed-04a0-4129-9507-2194687199af

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_insertCollisionAux_unique_updated
public import Theorems.Thm_VerifiedHAMT_insertEntries_unique_updated

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (hu : Unique node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    Unique res ∧ Updated node res key value := by
  induction wf generalizing key value with
  | collision hashAt keys vals hsz =>
    rw [insertNoExpand.eq_def]
    cases hu with
    | collision distinct =>
      exact insertCollisionAux_unique_updated keys vals hsz distinct 0 key value (by omega)
  | @entries hashAt es hs route children ih =>
    rw [insertNoExpand.eq_def]
    apply insertEntries_unique_updated hashAt es _ key value (.entries hs route children) hu
    grind [Array.mem_iff_getElem]
end VerifiedHAMT
