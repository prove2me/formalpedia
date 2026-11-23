-- Prove2me | solution 1 for VerifiedHAMT.findCollisionAux_eq_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:35.896053+00:00
-- url     : https://prove2.me/submissions/d87940fd-ebd6-423e-a341-597a3a5e95fc

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
    (i : Nat) (key : α) :
    findCollisionAux keys vals hsz i key = none ↔
      ∀ (j : Nat) (hj : j < keys.size), i ≤ j → keys[j] ≠ key := by
  rw [findCollisionAux]
  split
  · rename_i hi
    split
    · rename_i hk
      exact ⟨nofun, fun h => absurd (LawfulBEq.eq_of_beq hk).symm (h i hi (Nat.le_refl _))⟩
    · rename_i hk
      rw [solution keys vals hsz (i + 1) key]
      constructor
      · intro h j hj hij heq
        rcases Nat.eq_or_lt_of_le hij with rfl | hlt
        · exact hk (beq_iff_eq.mpr heq.symm)
        · exact h j hj hlt heq
      · intro h j hj hij
        exact h j hj (Nat.le_of_succ_le hij)
  · rename_i hi
    exact ⟨fun _ j hj hij => absurd (Nat.lt_of_le_of_lt hij hj) hi, fun _ => rfl⟩
termination_by keys.size - i
end VerifiedHAMT
