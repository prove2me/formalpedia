-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.hasKey_set_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:46.859771+00:00
-- url     : https://prove2.me/submissions/e3f9d6e6-87df-4fb2-bd3e-77e62fa5019a

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {es : Array (Entry α (Node α))}
    (i : Nat) (hi : i < es.size) (e : Entry α (Node α)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by
  simp [hasKey_entries, Array.getElem_set]
  grind
end VerifiedHAMT.SetWithoutValArray.Raw
