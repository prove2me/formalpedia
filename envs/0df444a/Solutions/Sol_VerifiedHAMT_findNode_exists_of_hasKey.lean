-- Prove2me | solution 1 for VerifiedHAMT.findNode_exists_of_hasKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:37.764338+00:00
-- url     : https://prove2.me/submissions/d20faa25-eb07-4dc1-9ebc-1cbd29cf84a7

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
public import Theorems.Thm_VerifiedHAMT_findNode_entries
public import Theorems.Thm_VerifiedHAMT_findCollisionAux_eq_none_iff
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : ∃ value, findNode node (hashAt key) key = some value := by
  induction wf with
  | collision hashAt keys vals hsz =>
    have hk := hasKey_collision.mp member
    have hn : findCollisionAux keys vals hsz 0 key ≠ none := by
      intro hn
      have hall := (findCollisionAux_eq_none_iff keys vals hsz 0 key).mp hn
      obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hk
      exact hall i hi (Nat.zero_le _) he
    cases he : findCollisionAux keys vals hsz 0 key with
    | none => exact False.elim (hn he)
    | some value => exact ⟨value, by simpa only [findNode] using he⟩
  | @entries hashAt es hs routing children ih =>
    obtain ⟨i, hi, hk⟩ := hasKey_entries.mp member
    have hslot := routing i hi key hk
    subst i
    rw [findNode_entries, dif_pos hi]
    cases he : es[slot (hashAt key)] with
    | null => simp [he, EntryHasKey] at hk
    | entry key' value =>
      have heq : key = key' := by simpa [he, EntryHasKey] using hk
      exact ⟨value, by simp [heq]⟩
    | ref child =>
      exact ih _ hi child he (by simpa [he, EntryHasKey] using hk)
end VerifiedHAMT
