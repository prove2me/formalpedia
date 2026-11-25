-- Prove2me | solution 1 for SmallRatio.one_le_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:27:01.44946+00:00
-- url     : https://prove2.me/submissions/c1cda197-c391-478f-8000-62092b7ef905

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_steps_spec
attribute [local simp] SmallRatio.rem_zero

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
omit hc
namespace SmallRatio
theorem _root_.solution : 1 ≤ steps k h := by
  by_contra h0
  have h0 : steps k h = 0 := by omega
  have := steps_spec hhk
  rw [h0, rem_zero] at this
  omega
end SmallRatio
