-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertNode_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:33.030429+00:00
-- url     : https://prove2.me/submissions/1a5b0a1a-ae21-4e59-9d23-ed0ef719cfe9

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertCollisionAux_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertEntries_wf_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNoExpand_wf_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_rebuild_wf_mem
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_empty
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hash_shift_offset
public import Theorems.Thm_VerifiedHAMT_offset_add_shift
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
    (key : α) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction levels generalizing offset node key with
  | zero => exact insertNoExpand_wf_mem wf key
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childSpec := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childSpec
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_wf_mem _ es _ key wf
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys =>
      simp only [insertNode]
      generalize hc : insertCollision keys key = b
      have hm (q : α) : HasKey q b.val ↔ q = key ∨ HasKey q (.collision keys) := by
        rw [← hc]
        exact insertCollisionAux_mem keys 0 key q
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' =>
        simp only [getCollisionNodeSize]
        by_cases hlt : keys'.size < Lean.PersistentHashMap.maxCollisions <;> simp only [hlt, ↓reduceIte]
        · exact ⟨.collision _ _, hm⟩
        · have rebuilt := rebuild_wf_mem (insertNode levels (offset + shift)) offset childSpec
            keys' 0 mkEmptyEntriesArray (wellFormed_empty _)
          refine ⟨rebuilt.1, ?_⟩
          intro q
          rw [rebuilt.2]
          simpa [hasKey_entries, hasKey_collision, mkEmptyEntriesArray, EntryHasKey, ← Array.mem_iff_getElem] using hm q
end VerifiedHAMT.SetWithoutValArray.Raw
