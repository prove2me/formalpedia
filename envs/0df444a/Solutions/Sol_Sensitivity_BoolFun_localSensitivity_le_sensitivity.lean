-- Prove2me | solution 1 for Sensitivity.BoolFun.localSensitivity_le_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:54:48.578647+00:00
-- url     : https://prove2.me/submissions/afb51a6e-13b4-411d-a7f6-3aa857804adc

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_Sensitivity_Defs

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ f.sensitivity := by
  exact Finset.le_sup (f := fun x => f.localSensitivity x) (Finset.mem_univ x)
end BoolFun
end Sensitivity
