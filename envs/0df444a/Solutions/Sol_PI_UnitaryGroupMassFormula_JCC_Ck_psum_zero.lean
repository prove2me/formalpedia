-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.psum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:26.848976+00:00
-- url     : https://prove2.me/submissions/61fa2ff4-f506-4605-ad2f-a4f0847c3894

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
variable {d : ℕ}
namespace PI.UnitaryGroupMassFormula.JCC.Ck
theorem _root_.solution (y h : Fin d → ℝ) : psum y h 0 = y := by
  funext l
  simp [psum]
end PI.UnitaryGroupMassFormula.JCC.Ck
