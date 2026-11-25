-- Prove2me | solution 1 for PI.SSE.lattice_span_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:27.516136+00:00
-- url     : https://prove2.me/submissions/3d57bfca-160c-40fe-a558-ec1e6aef58a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Reduce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (x y : ℂ) : PI.lat2 x y = PI.lat2 y x := by
  unfold PI.lat2
  rw [Set.pair_comm]
end PI.SSE
