-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.hasKey_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:31:37.647221+00:00
-- url     : https://prove2.me/submissions/00b1ba0b-6f24-4e65-99bc-38199d78c760

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {keys : Array α} {key : α} :
    HasKey key (.collision keys) ↔ key ∈ keys := by
  constructor
  · intro h; cases h with | collision h => exact h
  · exact HasKey.collision
end VerifiedHAMT.SetWithoutValArray.Raw
