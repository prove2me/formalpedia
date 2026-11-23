-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.WellFormed.slot_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:47.150818+00:00
-- url     : https://prove2.me/submissions/89cc71f9-b8f6-44e5-8caf-939f19800583

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_lt_branching

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
namespace WellFormed
theorem _root_.solution {hashAt : α → USize}
    {es : Array (Entry α (Node α))} (wf : WellFormed hashAt (.entries es))
    (hash : USize) : slot hash < es.size := by
  cases wf with
  | entries size_eq _ _ => simpa only [size_eq] using slot_lt_branching hash
end WellFormed
end VerifiedHAMT.SetWithoutValArray.Raw
