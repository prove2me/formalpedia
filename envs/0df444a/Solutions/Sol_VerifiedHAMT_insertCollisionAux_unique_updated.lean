-- Prove2me | solution 1 for VerifiedHAMT.insertCollisionAux_unique_updated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:10.131344+00:00
-- url     : https://prove2.me/submissions/c2943da6-780e-4138-bab9-1c048f66c2e1

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_collision_push_binding
public import Theorems.Thm_VerifiedHAMT_hasBinding_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_collision


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (hu : DistinctKeys keys) (i : Nat) (key : α) (value : β)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    letI res := insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value
    Unique res.val ∧ Updated (.collision keys vals hsz) res.val key value := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · constructor
      · apply Unique.collision
        grind [Array.set_getElem_self]
      · intro q w
        simp only [hasBinding_collision, Array.size_set, Array.getElem_set]
        grind [DistinctKeys]
    · apply solution keys vals hsz hu (i + 1) key value
      grind
  · rename_i hi
    have fresh : key ∉ keys := by grind [Array.mem_iff_getElem]
    constructor
    · exact .collision (hu.push fresh)
    · intro q w
      rw [collision_push_binding keys vals hsz]
      grind [→ HasBinding.hasKey, hasKey_collision]
termination_by keys.size - i
end VerifiedHAMT
