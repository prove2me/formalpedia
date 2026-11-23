-- Prove2me | solution 1 for VerifiedHAMT.WellFormed.slot_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:09.216787+00:00
-- url     : https://prove2.me/submissions/afd50143-b25d-4dfb-a279-064e37fd818d

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
public import Theorems.Thm_VerifiedHAMT_slot_lt_branching
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
namespace WellFormed
theorem _root_.solution {hashAt : α → USize}
    {es : Array (Entry α β (Node α β))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by
  cases wf with
  | entries size_eq _ _ => simpa only [size_eq] using slot_lt_branching hash
end WellFormed
end VerifiedHAMT
