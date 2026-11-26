-- Prove2me | solution 1 for P2M_FriedCrossing_TorsionCore_det_D_mat_fc25e0bffca9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:43:39.339477+00:00
-- url     : https://prove2.me/submissions/3edca6ea-2d41-4f00-9cb1-21175664b957

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution : (D₂mat : Matrix (Fin 3) (Fin 3) K).det = -1 := by
  rw [D₂mat, det_transpose, det_fin_three]
  simp [d₁]
end FriedCrossing.TorsionCore
