-- Prove2me | solution 1 for Sensitivity.BoolFun.sensitivity_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:31.875462+00:00
-- url     : https://prove2.me/submissions/2dc835d9-b37f-4372-97f8-d1e69947aa90

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Basic
import Theorems.Thm_Sensitivity_BoolFun_localSensitivity_not

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) :
    BoolFun.sensitivity (fun y => !f y) = f.sensitivity := by
  unfold sensitivity
  congr 1
  funext x
  exact f.localSensitivity_not x
end BoolFun
end Sensitivity
