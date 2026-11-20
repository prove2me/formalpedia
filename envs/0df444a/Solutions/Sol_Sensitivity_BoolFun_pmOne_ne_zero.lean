-- Prove2me | solution 1 for Sensitivity.BoolFun.pmOne_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:42.791732+00:00
-- url     : https://prove2.me/submissions/5114f9df-ba87-4b6e-8e6f-f121552362ac

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (x : Fin n → Bool) :
    f.pmOne x ≠ 0 := by
  unfold pmOne; split <;> omega
end BoolFun
end Sensitivity
