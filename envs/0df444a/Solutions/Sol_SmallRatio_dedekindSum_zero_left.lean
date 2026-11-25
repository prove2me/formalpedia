-- Prove2me | solution 1 for SmallRatio.dedekindSum_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:23:11.225543+00:00
-- url     : https://prove2.me/submissions/da492868-6091-494e-a204-2d433f671d43

module
public import Definitions.Def_SmallRatio_Main
public import Definitions.Def_SmallRatio_Subgroup
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_zero
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p : ℕ}
namespace SmallRatio
theorem _root_.solution (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum, sawtooth]
end SmallRatio
