-- Prove2me | solution 1 for VerifiedHAMT.findNode_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:17.784129+00:00
-- url     : https://prove2.me/submissions/e73c2dd9-23b6-4960-84e0-b4751b819f5d

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_entries
public import Theorems.Thm_VerifiedHAMT_findCollisionAux_sound

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] (node : Node α β)
    (hash : USize) (key : α) (value : β) (found : findNode node hash key = some value) :
    HasBinding key value node := by
  cases node with
  | collision keys vals hsz =>
    rw [findNode] at found
    obtain ⟨i, hi, _, hk, hv⟩ :=
      findCollisionAux_sound keys vals hsz 0 key value found
    exact .collision hi hk hv
  | entries es =>
    rw [findNode_entries] at found
    split at found
    · rename_i hi
      split at found
      · contradiction
      · rename_i key' val he
        split at found
        · rename_i hk
          have heq : key = key' := eq_of_beq hk
          have hv : val = value := Option.some.inj found
          subst key'; subst val
          exact .entry he
        · contradiction
      · rename_i child he
        have hlt : sizeOf child < sizeOf es := by
          have h := Array.sizeOf_get es (slot hash) hi
          rw [he] at h
          simp at h
          omega
        exact .ref he (solution child (nextHash hash) key value found)
    · contradiction
termination_by sizeOf node
decreasing_by simp_all; omega
end VerifiedHAMT
