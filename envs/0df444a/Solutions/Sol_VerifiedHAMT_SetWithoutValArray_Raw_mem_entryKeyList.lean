-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.mem_entryKeyList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:40.623454+00:00
-- url     : https://prove2.me/submissions/9e8f2dc8-965c-4db5-bf47-4be5fc4a2e0a

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {key : α} {e : Entry α (Node α)}
    (child : ∀ c, e = .ref c → (key ∈ keyList c ↔ HasKey key c)) :
    key ∈ entryKeyList e ↔ EntryHasKey key e := by
  cases e with
  | null => simp [entryKeyList, EntryHasKey]
  | entry k => simp [entryKeyList, EntryHasKey]
  | ref c => simpa [entryKeyList, EntryHasKey] using child c rfl
end VerifiedHAMT.SetWithoutValArray.Raw
