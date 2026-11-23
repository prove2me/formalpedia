-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.insertCollisionAux_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:58.301517+00:00
-- url     : https://prove2.me/submissions/95c4dddc-3c59-4467-8c23-4095046d0cbb

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Insert
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertSized

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth maxCollisions)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] (keys : Array α) (i : Nat) (key : α) :
    getCollisionNodeSize (insertCollisionAux ⟨.collision keys, .mk ..⟩ i key) =
      if (keys.drop i).contains key then keys.size else keys.size + 1 := by
  rw [insertCollisionAux.eq_def]
  dsimp only
  split
  · rename_i hi
    have step : (keys.drop i).contains key =
        ((key == keys[i]) || (keys.drop (i + 1)).contains key) := by
      have contains_drop (j : Nat) :
          (keys.drop j).contains key = (keys.toList.drop j).contains key := by
        simpa only [List.toArray_drop, Array.toArray_toList] using
          (List.contains_toArray (l := keys.toList.drop j) (a := key))
      simp only [contains_drop]
      have hs := congrArg (fun xs : List α => xs.contains key)
        (List.drop_eq_getElem_cons (l := keys.toList) (i := i) (by simpa using hi))
      simp only [List.contains_cons] at hs
      rw [Array.getElem_toList] at hs
      exact hs
    rw [step]
    split
    · simp_all [getCollisionNodeSize]
    · rename_i hk
      simpa [hk] using solution keys (i + 1) key
  · rename_i hi
    simp [getCollisionNodeSize, Array.extract_empty_of_size_le_start (by omega : keys.size ≤ i)]
termination_by keys.size - i
end VerifiedHAMT.SetWithoutValArray.Raw
