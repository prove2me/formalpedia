-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.keyCount_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:05.464687+00:00
-- url     : https://prove2.me/submissions/d49f018a-8d1d-4993-87fb-8c7917253dc0

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_unique_insert
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_contains_eq_true_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_insert_iff
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_keyList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_nodup_keyList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_insert


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    keyCount (insert set key).root =
      if contains set key then keyCount set.root else keyCount set.root + 1 := by
  have wf' := valid_insert set wf key
  have hnodup := nodup_keyList wf hu
  have hnodup' := nodup_keyList wf' (unique_insert set wf hu key)
  have hmem : ∀ q, q ∈ keyList (insert set key).root ↔ q = key ∨ q ∈ keyList set.root := by
    intro q
    rw [mem_keyList wf' q, mem_keyList wf q]
    exact mem_insert_iff set wf key q
  have h_len_eq : ∀ {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁.length = l₂.length :=
    fun h₁ h₂ h => (List.perm_iff_count.mpr fun a => by simp only [h₁.count, h₂.count, h a]).length_eq
  unfold keyCount
  split
  · rename_i hc
    have hk : key ∈ keyList set.root :=
      (mem_keyList wf key).mpr ((contains_eq_true_iff set wf key).mp hc)
    apply h_len_eq hnodup' hnodup
    grind
  · rename_i hc
    have hk : key ∉ keyList set.root := fun h =>
      hc ((contains_eq_true_iff set wf key).mpr ((mem_keyList wf key).mp h))
    rw [← List.length_cons]
    apply h_len_eq hnodup' (List.nodup_cons.mpr ⟨hk, hnodup⟩)
    grind
end VerifiedHAMT.SetWithoutValArray.Raw
