-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.unique_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:42:30.737091+00:00
-- url     : https://prove2.me/submissions/1c22d7f9-7a25-4b0d-8e8c-57cabb83dc20

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
theorem _root_.solution {k₁ k₂ : α} (hne : k₁ ≠ k₂) :
    Unique (mkCollisionNode k₁ k₂) := by
  apply Unique.collision
  intro i hi j hj
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  have hj' : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp_all [Ne.symm hne]
end VerifiedHAMT.SetWithoutValArray.Raw
