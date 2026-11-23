-- Prove2me | solution 1 for VerifiedHAMT.root_offset_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:00.985403+00:00
-- url     : https://prove2.me/submissions/0c9b2a66-bd15-447c-b723-f5446e95ccff

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
theorem _root_.solution : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
  rcases System.Platform.numBits_eq with hb | hb <;>
    simp [maxDepth, USize.toNat_ofNat, hb]
end VerifiedHAMT
