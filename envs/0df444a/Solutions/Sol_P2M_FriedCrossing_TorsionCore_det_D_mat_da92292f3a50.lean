-- Prove2me | solution 1 for P2M_FriedCrossing_TorsionCore_det_D_mat_da92292f3a50
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:43:43.709842+00:00
-- url     : https://prove2.me/submissions/9bf09c8d-b3a4-40df-bf86-37bce3eedeec

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (l : K) : (D₄mat l).det = l := by
  rw [D₄mat, det_transpose, det_fin_one]
  simp [d₃]
end FriedCrossing.TorsionCore
