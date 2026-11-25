-- Prove2me | solution 1 for SCCThm8.cntLift_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:06.99591+00:00
-- url     : https://prove2.me/submissions/3b8b1cfd-9020-45fb-89e9-7e30c5bd7473

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
    -1 ≤ cntLift v i ∧ cntLift v i ≤ 1 := by
  unfold cntLift
  split_ifs <;> norm_num
end SCCThm8
