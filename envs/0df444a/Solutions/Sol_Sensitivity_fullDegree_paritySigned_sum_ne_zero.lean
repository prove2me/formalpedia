-- Prove2me | solution 1 for Sensitivity.fullDegree_paritySigned_sum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:59.318715+00:00
-- url     : https://prove2.me/submissions/55ba8091-b3ef-4fd9-a4c5-71d6883457e8

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
import Theorems.Thm_Sensitivity_moebius_parity_sum

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (f : BoolFun n) (hn : 0 < n)
    (h : f.moebius Finset.univ ≠ 0) :
    ∑ x : Fin n → Bool, f.paritySigned x ≠ 0 := by
  rw [moebius_parity_sum _ hn]
  apply mul_ne_zero
  apply mul_ne_zero
  · omega
  · positivity
  · exact h
end Sensitivity
