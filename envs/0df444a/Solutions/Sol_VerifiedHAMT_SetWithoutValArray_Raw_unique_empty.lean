-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.unique_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:53.833808+00:00
-- url     : https://prove2.me/submissions/e3fe1ae1-8344-410e-8437-ea5fa785c22d

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
theorem _root_.solution : Unique (mkEmptyEntries : Node α) := by
  apply Unique.entries
  intro i hi child hc
  simp [mkEmptyEntriesArray] at hc
end VerifiedHAMT.SetWithoutValArray.Raw
