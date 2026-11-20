-- Prove2me | solution 1 for Sensitivity.BoolFun.localSensitivity_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:57.535617+00:00
-- url     : https://prove2.me/submissions/a2eac858-2e51-4b42-889b-eac83cb2d4b3

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) :
    BoolFun.localSensitivity (fun y => !f y) x = f.localSensitivity x := by
  unfold localSensitivity sensitiveAt
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  cases hflip : f (flipBit x i) <;> cases hcurrent : f x <;> simp [hflip, hcurrent]
end BoolFun
end Sensitivity
