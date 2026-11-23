-- Prove2me | solution 1 for VerifiedHAMT.offset_add_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:18.384718+00:00
-- url     : https://prove2.me/submissions/e7d3d02f-3816-4b99-a48a-ed6d238cc356

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_Util

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap (shift maxDepth)
namespace VerifiedHAMT
theorem _root_.solution (offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    (offset + shift).toNat = offset.toNat + 5 := by
  change (offset + 5).toNat = offset.toNat + 5
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp only [USize.toNat_add, USize.toNat_ofNat, hb, Nat.reducePow, Nat.reduceMod] <;>
    exact Nat.mod_eq_of_lt (by omega)
end VerifiedHAMT
