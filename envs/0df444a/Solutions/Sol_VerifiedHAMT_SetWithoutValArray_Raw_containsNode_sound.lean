-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.containsNode_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:01.620184+00:00
-- url     : https://prove2.me/submissions/2becbb3e-5ab2-49b2-8b28-d78404b4ebd2

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_collision


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] (node : Node α)
    (hash : USize) (key : α) (found : containsNode node hash key = true) :
    HasKey key node := by
  cases node with
  | collision keys =>
    rw [hasKey_collision]
    simp [containsNode] at found
    exact found
  | entries es =>
    by_cases hi : slot hash < es.size
    · rw [containsNode, dif_pos hi] at found
      split at found
      · contradiction
      · rename_i key' he
        have heq : key = key' := by simpa using found
        subst key'
        exact HasKey.entry he
      · rename_i child he
        have hlt : sizeOf child < sizeOf es := by
          have h := Array.sizeOf_get es (slot hash) hi
          rw [he] at h
          simp at h
          omega
        apply HasKey.ref he
        exact solution child (nextHash hash) key found
    · simp [containsNode, hi] at found
termination_by sizeOf node
decreasing_by simp_all; omega
end VerifiedHAMT.SetWithoutValArray.Raw
