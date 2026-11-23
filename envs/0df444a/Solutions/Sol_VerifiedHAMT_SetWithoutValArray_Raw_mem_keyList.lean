-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.mem_keyList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:02.988221+00:00
-- url     : https://prove2.me/submissions/6ba6b7d0-bc87-4c8f-903d-7ee7a0978330

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_entries
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_entryKeyList
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {hashAt : α → USize} {node : Node α} (wf : WellFormed hashAt node)
    (key : α) : key ∈ keyList node ↔ HasKey key node := by
  induction wf generalizing key with
  | collision hashAt keys => simp [hasKey_collision]
  | @entries hashAt es size_eq routing children ih =>
    rw [keyList_entries, hasKey_entries, List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hk⟩
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp he)
      exact ⟨i, hi, (mem_entryKeyList fun c hc => ih i hi c hc key).mp hk⟩
    · rintro ⟨i, hi, hk⟩
      exact ⟨es[i], Array.getElem_mem_toList hi,
        (mem_entryKeyList fun c hc => ih i hi c hc key).mpr hk⟩
end VerifiedHAMT.SetWithoutValArray.Raw
