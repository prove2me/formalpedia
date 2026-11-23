-- Prove2me | solution 1 for VerifiedHAMT.containsNode_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:07.240815+00:00
-- url     : https://prove2.me/submissions/ff1625fe-2d27-41a1-bacf-fcdfc431da65

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_hasKey_collision


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (found : containsNode node hash key = true) :
    HasKey key node := by
  cases node with
  | collision keys vals hsz =>
    rw [hasKey_collision]
    simp [containsNode] at found
    exact found
  | entries es =>
    by_cases hi : slot hash < es.size
    · rw [containsNode, dif_pos hi] at found
      split at found
      · contradiction
      · rename_i key' value he
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
end VerifiedHAMT
