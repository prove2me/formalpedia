-- Prove2me | solution 1 for SCCThm8.mem_iff_cntLift_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:09.314987+00:00
-- url     : https://prove2.me/submissions/f50a1e87-3352-4765-a492-9548f96a6c5d

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (v : Finset (Fin n)) (i : Fin n) :
    i ∈ v ↔ cntLift v i ≠ 0 := by
  unfold cntLift
  split_ifs <;> simp_all
end SCCThm8
