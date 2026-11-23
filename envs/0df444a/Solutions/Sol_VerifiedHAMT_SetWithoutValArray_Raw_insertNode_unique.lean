-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertNode_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:46.886829+00:00
-- url     : https://prove2.me/submissions/1ea6ccc2-3c82-40ba-ba48-dba65936695c

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNoExpand_unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_rebuild_unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNode_wf_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_empty
public import Theorems.Thm_VerifiedHAMT_hash_shift_offset
public import Theorems.Thm_VerifiedHAMT_offset_add_shift
public import Theorems.Thm_VerifiedHAMT_unique_empty
public import Theorems.Thm_VerifiedHAMT_wellFormed_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (hu : Unique node) (key : α) :
    Unique (insertNode levels offset node ((hash key).toUSize >>> offset) key) := by
  induction levels generalizing offset node key with
  | zero => exact insertNoExpand_unique wf hu key
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childWF := insertNode_wf_mem (α := α) levels (offset + shift) hn
    have childUnique := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childWF childUnique
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_unique _ es _ key wf hu
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys =>
      have distinct : DistinctKeys keys := by cases hu with | collision h => exact h
      have ub := insertCollisionAux_unique keys distinct 0 key (by omega)
      rw [← insertCollision.eq_def] at ub
      simp only [insertNode]
      generalize hc : insertCollision keys key = b at ub ⊢
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' =>
        simp only [getCollisionNodeSize]
        by_cases hlt : keys'.size < Lean.PersistentHashMap.maxCollisions <;> simp only [hlt, ↓reduceIte]
        · exact ub
        · exact rebuild_unique (insertNode levels (offset + shift)) offset
            childWF childUnique keys' 0 mkEmptyEntriesArray (wellFormed_empty _) unique_empty
end VerifiedHAMT.SetWithoutValArray.Raw
