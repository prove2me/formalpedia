-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:47.568218+00:00
-- url     : https://prove2.me/submissions/97f38b50-779e-4061-9269-3d1359e1202b

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Definitions.Def_VerifiedHAMT_Util
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_collision


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α]
    (keys : Array α)
    (i : Nat) (key q : α) :
    HasKey q (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val ↔
      q = key ∨ HasKey q (.collision keys) := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · grind [hasKey_collision, Array.set_getElem_self]
    · exact solution keys (i + 1) key q
  · simp [hasKey_collision, or_comm]
termination_by keys.size - i
end VerifiedHAMT.SetWithoutValArray.Raw
