-- Prove2me | solution 1 for Sensitivity.BoolFun.sensitiveAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:57.989277+00:00
-- url     : https://prove2.me/submissions/cc22bcac-e7b1-4536-a941-6f1295594972

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt x i ↔ f (flipBit x i) ≠ f x :=
  Iff.rfl
end BoolFun
end Sensitivity
