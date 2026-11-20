-- Prove2me | solution 1 for Sensitivity.BoolFun.sensitiveAt_flipBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:08.382857+00:00
-- url     : https://prove2.me/submissions/8a733073-d6d1-4772-a73c-7ab5a9c602c1

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_flipBit_same



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt (flipBit x i) i ↔ f.sensitiveAt x i := by
  unfold sensitiveAt
  rw [flipBit_flipBit_same]
  exact ne_comm
end BoolFun
end Sensitivity
