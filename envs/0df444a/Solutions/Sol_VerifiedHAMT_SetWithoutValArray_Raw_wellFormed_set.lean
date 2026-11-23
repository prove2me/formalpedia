-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:42:25.737807+00:00
-- url     : https://prove2.me/submissions/306ea699-6ae1-4a4e-ba49-52a4fae11021

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_valid_empty

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.valid_empty
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.not_mem_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {hashAt : α → USize} {es : Array (Entry α (Node α))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by
  cases wf with
  | entries size_eq routing children =>
    apply WellFormed.entries (by simpa using size_eq) <;> grind
end VerifiedHAMT.SetWithoutValArray.Raw
