-- Prove2me | solution 1 for VerifiedHAMT.keyList_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:48.305803+00:00
-- url     : https://prove2.me/submissions/d9b84313-0186-421c-88f9-f5e3fd3af32f

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
public import Theorems.Thm_VerifiedHAMT_entryListKeyList_eq_flatMap

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution (es : Array (Entry α β (Node α β))) :
    keyList (.entries es) = es.toList.flatMap entryKeyList := by
  cases es with
  | mk es => simp [keyList, entriesKeyList, entryListKeyList_eq_flatMap]
end VerifiedHAMT
