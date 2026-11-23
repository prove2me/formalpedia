-- Prove2me | solution 1 for VerifiedHAMT.findCollisionAux_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:21.489501+00:00
-- url     : https://prove2.me/submissions/1d4ea4e9-5af9-441f-bd03-1c7f71cf93d5

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α]
    (keys : Array α) (vals : Array β) (hsz : keys.size = vals.size)
    (i : Nat) (key : α) (value : β)
    (found : findCollisionAux keys vals hsz i key = some value) :
    ∃ (j : Nat) (hj : j < keys.size), i ≤ j ∧ keys[j] = key ∧
      vals[j]'(hsz ▸ hj) = value := by
  rw [findCollisionAux] at found
  split at found
  · rename_i hi
    split at found
    · rename_i hk
      exact ⟨i, hi, Nat.le_refl _, (LawfulBEq.eq_of_beq hk).symm, Option.some.inj found⟩
    · obtain ⟨j, hj, hij, hk, hv⟩ :=
        solution keys vals hsz (i + 1) key value found
      exact ⟨j, hj, by omega, hk, hv⟩
  · contradiction
termination_by keys.size - i
end VerifiedHAMT
