-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.push
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:43.54255+00:00
-- url     : https://prove2.me/submissions/166107b9-28ba-4df0-969f-3ad995f0e887

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_valid_empty
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_DistinctKeys_push
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
namespace DistinctKeys
theorem _root_.solution {keys : Array α} (hu : DistinctKeys keys)
    {key : α} (fresh : key ∉ keys) : DistinctKeys (keys.push key) := by
  intro i hi j hj he ; simp [DistinctKeys] at hu ; grind
end DistinctKeys
end VerifiedHAMT.SetWithoutValArray.Raw
