-- Prove2me | solution 1 for P2M_FriedCrossing_TorsionCore_det_D_mat_4a6a93f491c6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:43:43.243151+00:00
-- url     : https://prove2.me/submissions/1a3d00ed-e977-4743-88bc-d583708e010d

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (x l : K) : (D₃mat x l).det = -(l + x) := by
  rw [D₃mat, det_transpose, det_fin_three]
  simp [d₂]
  ring
end FriedCrossing.TorsionCore
