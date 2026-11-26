-- Prove2me | solution 1 for P2M_FriedCrossing_TorsionCore_d__mul_d__23c2a68739a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:07.350402+00:00
-- url     : https://prove2.me/submissions/40d56880-c090-4af9-9d50-24ed42305035

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (x l : K) : d₂ x l * (d₁ : Matrix (Fin 3) (Fin 1) K) = 0 := by
  ext i j
  fin_cases j
  fin_cases i <;> simp [d₁, d₂, Matrix.mul_apply, Fin.sum_univ_succ]
end FriedCrossing.TorsionCore
