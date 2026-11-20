-- Prove2me | solution 1 for Sensitivity.BoolFun.degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:56:05.711033+00:00
-- url     : https://prove2.me/submissions/0e3707fd-39d7-4763-9528-35de42c29d80

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) : f.degree ≤ n := by
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter] at hS
  exact le_trans (Finset.card_le_univ S) (le_of_eq (Fintype.card_fin n))
end BoolFun
end Sensitivity
