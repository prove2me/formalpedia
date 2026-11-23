-- Prove2me | solution 1 for VerifiedHAMT.EntryHasBinding.hasKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:44.360077+00:00
-- url     : https://prove2.me/submissions/dd2cb237-7eda-4585-aae2-7717f789142e

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
namespace EntryHasBinding
theorem _root_.solution {q : α} {w : β} {e : Entry α β (Node α β)}
    (h : EntryHasBinding q w e) : EntryHasKey q e := by
  cases e with
  | null => exact h
  | entry k v => exact h.1
  | ref child => exact HasBinding.hasKey h
end EntryHasBinding
end VerifiedHAMT
