-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:59.360798+00:00
-- url     : https://prove2.me/submissions/a7b03eda-7c30-4bc5-a89c-ecd78f8502c1

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_DistinctKeys_push


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] (keys : Array α)
    (hu : DistinctKeys keys) (i : Nat) (key : α)
    (scanned : ∀ (j : Nat) (hj : j < keys.size), j < i → keys[j] ≠ key) :
    Unique (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key).val := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    split
    · apply Unique.collision
      grind [Array.set_getElem_self]
    · apply solution keys hu (i + 1) key
      grind
  · have fresh : key ∉ keys := by grind [Array.mem_iff_getElem]
    exact .collision (hu.push fresh)
termination_by keys.size - i
end VerifiedHAMT.SetWithoutValArray.Raw
