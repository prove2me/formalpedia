-- Prove2me | solution 1 for VerifiedHAMT.hash_shift_offset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:17.630407+00:00
-- url     : https://prove2.me/submissions/fde23d28-535a-40ba-851a-5f822e1dedb3

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
theorem _root_.solution (h offset : USize) (bound : offset.toNat + 5 ≤ 30) :
    h >>> (offset + shift) = nextHash (h >>> offset) := by
  change h >>> (offset + 5) = (h >>> offset) >>> (5 : USize)
  apply USize.toNat_inj.mp
  rcases System.Platform.numBits_eq with hb | hb
  all_goals
    simp only [USize.toNat_shiftRight, USize.toNat_add, USize.toNat_ofNat, hb]
    have ho : offset.toNat < System.Platform.numBits := by omega
    have hs : offset.toNat + 5 < System.Platform.numBits := by omega
    simp only [hb] at ho hs
    simp only [Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : offset.toNat + 5 < _), Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt ho, Nat.shiftRight_add]
end VerifiedHAMT
