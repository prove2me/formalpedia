-- Prove2me | solution 1 for VerifiedHAMT.insertCollisionAux_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:54.104328+00:00
-- url     : https://prove2.me/submissions/198b22bf-6117-4448-a421-94d60e98b18a

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_hasKey_collision


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key q : α) (value : β) :
    HasKey q (insertCollisionAux ⟨.collision keys vals hsz, .mk ..⟩ i key value).val ↔
      q = key ∨ HasKey q (.collision keys vals hsz) := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · grind [hasKey_collision, Array.set_getElem_self]
    · exact solution keys vals hsz (i + 1) key q value
  · simp [hasKey_collision, or_comm]
termination_by keys.size - i
end VerifiedHAMT
