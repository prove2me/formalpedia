-- Prove2me | solution 1 for Sensitivity.parity_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:42.231857+00:00
-- url     : https://prove2.me/submissions/1dbdd1b4-663d-4566-9e0d-516c1da2efd3

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
theorem _root_.solution (x : Fin n → Bool) : parity x ≠ 0 := by
  unfold parity; positivity
end Sensitivity
