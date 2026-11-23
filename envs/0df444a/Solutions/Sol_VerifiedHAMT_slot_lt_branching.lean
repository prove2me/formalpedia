-- Prove2me | solution 1 for VerifiedHAMT.slot_lt_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:42.43657+00:00
-- url     : https://prove2.me/submissions/9dcfacac-2e70-48c6-b961-2574ac85c677

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
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
theorem _root_.solution (hash : USize) : slot hash < branching.toNat := by
  have h : hash.toNat &&& 31 ≤ 31 := Nat.and_le_right
  unfold slot mod2Shift
  change (hash &&& ((1 : USize) <<< 5 - 1)).toNat < branching.toNat
  rw [USize.toNat_and]
  rcases System.Platform.numBits_eq with hb | hb <;>
    simpa [branching, shift, USize.toNat_sub, USize.toNat_shiftLeft, hb] using
      Nat.lt_succ_of_le h
end VerifiedHAMT
