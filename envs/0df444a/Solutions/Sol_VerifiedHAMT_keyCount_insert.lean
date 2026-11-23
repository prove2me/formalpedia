-- Prove2me | solution 1 for VerifiedHAMT.keyCount_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:03.48548+00:00
-- url     : https://prove2.me/submissions/09050524-01a4-4240-8dc0-a61de0078890

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_valid_insert
public import Theorems.Thm_VerifiedHAMT_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_unique_insert
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_insert_self
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_mem_keyList
public import Theorems.Thm_VerifiedHAMT_nodup_keyList

attribute [local simp] VerifiedHAMT.mapsTo_insert_self
attribute [local simp] VerifiedHAMT.contains_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key : α) (value : β) :
    keyCount (insert map key value).root =
      if contains map key then keyCount map.root else keyCount map.root + 1 := by
  have wf' := valid_insert map wf key value
  have hnodup := nodup_keyList wf hu
  have hnodup' := nodup_keyList wf' (unique_insert map wf hu key value)
  have hmem : ∀ q, q ∈ keyList (insert map key value).root ↔ q = key ∨ q ∈ keyList map.root := by
    intro q
    rw [mem_keyList wf' q, mem_keyList wf q]
    exact mem_insert_iff map wf key q value
  have h_len_eq : ∀ {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁.length = l₂.length :=
    fun h₁ h₂ h => (List.perm_iff_count.mpr fun a => by simp only [h₁.count, h₂.count, h a]).length_eq
  unfold keyCount
  split
  · rename_i hc
    have hk : key ∈ keyList map.root :=
      (mem_keyList wf key).mpr ((contains_eq_true_iff map wf key).mp hc)
    apply h_len_eq hnodup' hnodup
    intro q
    rw [hmem]
    constructor
    · rintro (rfl | h) <;> assumption
    · exact Or.inr
  · rename_i hc
    have hk : key ∉ keyList map.root := fun h =>
      hc ((contains_eq_true_iff map wf key).mpr ((mem_keyList wf key).mp h))
    rw [← List.length_cons]
    apply h_len_eq hnodup' (List.nodup_cons.mpr ⟨hk, hnodup⟩)
    intro q
    rw [hmem, List.mem_cons]
end VerifiedHAMT
