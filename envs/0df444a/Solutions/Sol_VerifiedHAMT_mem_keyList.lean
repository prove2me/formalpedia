-- Prove2me | solution 1 for VerifiedHAMT.mem_keyList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:11.605479+00:00
-- url     : https://prove2.me/submissions/663b30b2-4769-4be0-b914-5144832638aa

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
public import Theorems.Thm_VerifiedHAMT_keyList_entries
public import Theorems.Thm_VerifiedHAMT_keyList_collision
public import Theorems.Thm_VerifiedHAMT_mem_entryKeyList
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries

attribute [local simp] VerifiedHAMT.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {hashAt : α → USize} {node : Node α β} (wf : WellFormed hashAt node)
    (key : α) : key ∈ keyList node ↔ HasKey key node := by
  induction wf generalizing key with
  | collision hashAt keys vals hsz => simp [hasKey_collision]
  | @entries hashAt es size_eq routing children ih =>
    rw [keyList_entries, hasKey_entries, List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hk⟩
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp he)
      exact ⟨i, hi, (mem_entryKeyList fun c hc => ih i hi c hc key).mp hk⟩
    · rintro ⟨i, hi, hk⟩
      exact ⟨es[i], Array.getElem_mem_toList hi,
        (mem_entryKeyList fun c hc => ih i hi c hc key).mpr hk⟩
end VerifiedHAMT
