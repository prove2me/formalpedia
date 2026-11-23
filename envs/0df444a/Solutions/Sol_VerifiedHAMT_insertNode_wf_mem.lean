-- Prove2me | solution 1 for VerifiedHAMT.insertNode_wf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:06.287803+00:00
-- url     : https://prove2.me/submissions/06fc748a-ca89-454c-a47a-4273a98c1c29

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
public import Theorems.Thm_VerifiedHAMT_insertNoExpand_wf_mem
public import Theorems.Thm_VerifiedHAMT_rebuild_wf_mem
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hash_shift_offset
public import Theorems.Thm_VerifiedHAMT_offset_add_shift
public import Theorems.Thm_VerifiedHAMT_wellFormed_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α] (levels : Nat)
    (offset : USize) (bound : offset.toNat + 5 * levels ≤ 30)
    (node : Node α β) (wf : WellFormed (fun k => (hash k).toUSize >>> offset) node)
    (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    WellFormed (fun k => (hash k).toUSize >>> offset) res ∧
      ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by
  induction levels generalizing offset node key value with
  | zero => exact insertNoExpand_wf_mem wf key value
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
      apply insertEntries_wf_mem _ es _ key value wf
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys vals hsz =>
      simp only [insertNode]
      generalize hc : insertCollision keys vals hsz key value = b
      have hm (q : α) : HasKey q b.val ↔ q = key ∨ HasKey q (.collision keys vals hsz) := by
        rw [← hc]
        exact insertCollisionAux_mem keys vals hsz 0 key q value
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' vals' hsz' =>
        simp only [getCollisionNodeSize]
        by_cases hlt : keys'.size < maxCollisions <;> simp only [hlt, ↓reduceIte]
        · exact ⟨.collision _ _ _ _, hm⟩
        · have rebuilt := rebuild_wf_mem (insertNode levels (offset + shift)) offset childSpec
            keys' vals' hsz' 0 mkEmptyEntriesArray (wellFormed_empty _)
          refine ⟨rebuilt.1, ?_⟩
          intro q
          rw [rebuilt.2]
          simpa [hasKey_entries, hasKey_collision, mkEmptyEntriesArray, EntryHasKey, ← Array.mem_iff_getElem] using hm q
end VerifiedHAMT
