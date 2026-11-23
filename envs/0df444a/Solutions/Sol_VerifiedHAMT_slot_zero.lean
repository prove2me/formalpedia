-- Prove2me | solution 1 for VerifiedHAMT.slot_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:12.235822+00:00
-- url     : https://prove2.me/submissions/948c4424-07d8-4d41-bc08-013fd1fca9a8

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution : slot 0 = 0 := by
  change ((0 : USize) &&& ((1 : USize) <<< shift - 1)).toNat = 0
  simp
end VerifiedHAMT
