-- Prove2me | solution 1 for P2M_FriedCrossing_TorsionCore_d__mul_d__53f55e44f3e8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:11.240854+00:00
-- url     : https://prove2.me/submissions/efa8ef95-b974-40a8-9c1f-7434a877ebdf

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (x l : K) : d₃ l * d₂ x l = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [d₃, d₂, Matrix.mul_apply, Fin.sum_univ_succ]
end FriedCrossing.TorsionCore
