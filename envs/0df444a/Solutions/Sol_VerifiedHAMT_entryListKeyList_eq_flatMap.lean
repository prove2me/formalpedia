-- Prove2me | solution 1 for VerifiedHAMT.entryListKeyList_eq_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:24.04393+00:00
-- url     : https://prove2.me/submissions/20fd31a4-a5c8-4f92-9883-4b07a152e19e

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution (es : List (Entry α β (Node α β))) :
    entryListKeyList es = es.flatMap entryKeyList := by
  induction es with
  | nil => simp [entryListKeyList]
  | cons e es ih => simp [entryListKeyList, ih]
end VerifiedHAMT
