-- Prove2me | solution 1 for VerifiedHAMT.insertNode_unique_updated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:38.29844+00:00
-- url     : https://prove2.me/submissions/eb1c154d-767e-4bb1-b8de-689088541396

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
public import Theorems.Thm_VerifiedHAMT_insertNoExpand_unique_updated
public import Theorems.Thm_VerifiedHAMT_insertNode_wf_mem
public import Theorems.Thm_VerifiedHAMT_rebuild_unique_bindings
public import Theorems.Thm_VerifiedHAMT_hasBinding_collision
public import Theorems.Thm_VerifiedHAMT_hasBinding_entries
public import Theorems.Thm_VerifiedHAMT_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hash_shift_offset
public import Theorems.Thm_VerifiedHAMT_offset_add_shift
public import Theorems.Thm_VerifiedHAMT_unique_empty
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
    (hu : Unique node) (key : α) (value : β) :
    letI res := insertNode levels offset node ((hash key).toUSize >>> offset) key value
    Unique res ∧ Updated node res key value := by
  induction levels generalizing offset node key value with
  | zero => exact insertNoExpand_unique_updated wf hu key value
  | succ levels ih =>
    have hb : offset.toNat + 5 ≤ 30 := by omega
    have hn : (offset + shift).toNat + 5 * levels ≤ 30 := by
      rw [offset_add_shift offset hb]
      omega
    have childWF := insertNode_wf_mem (α := α) (β := β) levels (offset + shift) hn
    have childUpd := ih (offset + shift) hn
    simp only [hash_shift_offset _ offset hb] at childWF childUpd
    cases node with
    | entries es =>
      simp only [insertNode]
      apply insertEntries_unique_updated _ es _ key value wf hu
      cases wf <;> grind [Array.mem_iff_getElem]
    | collision keys vals hsz =>
      have distinct : DistinctKeys keys := by cases hu with | collision h => exact h
      have uv := insertCollisionAux_unique_updated keys vals hsz distinct 0 key value (by omega)
      rw [← insertCollision.eq_def] at uv
      simp only [insertNode]
      generalize hc : insertCollision keys vals hsz key value = b at uv ⊢
      obtain ⟨node, hb⟩ := b
      cases hb with
      | mk keys' vals' hsz' =>
        simp only [getCollisionNodeSize]
        by_cases hlt : keys'.size < maxCollisions <;> simp only [hlt, ↓reduceIte]
        · exact uv
        · have distinct' : DistinctKeys keys' := by cases uv.1 with | collision h => exact h
          have rebuilt := rebuild_unique_bindings (insertNode levels (offset + shift)) offset
            childWF childUpd keys' vals' hsz' distinct' 0 mkEmptyEntriesArray
            (wellFormed_empty _) unique_empty (by
              intro j hj hij
              simp [hasKey_entries, mkEmptyEntriesArray, EntryHasKey])
          refine ⟨rebuilt.1, ?_⟩
          intro q w
          rw [rebuilt.2]
          simpa [hasBinding_entries, hasBinding_collision, mkEmptyEntriesArray, EntryHasBinding] using uv.2 q w
end VerifiedHAMT
