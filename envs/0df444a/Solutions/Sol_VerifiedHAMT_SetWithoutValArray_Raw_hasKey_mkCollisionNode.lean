-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.hasKey_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:33:42.651366+00:00
-- url     : https://prove2.me/submissions/9599022d-7114-4f28-80a6-d102537c6699

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_collision

attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (k₁ k₂ q : α) :
    HasKey q (mkCollisionNode k₁ k₂) ↔ q = k₁ ∨ q = k₂ := by
  simp [mkCollisionNode]
end VerifiedHAMT.SetWithoutValArray.Raw
