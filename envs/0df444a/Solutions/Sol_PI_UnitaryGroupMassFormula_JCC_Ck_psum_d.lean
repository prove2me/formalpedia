-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.psum_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:53.748246+00:00
-- url     : https://prove2.me/submissions/52426c15-2e4f-41aa-9b24-0ff2409dff30

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
theorem _root_.solution (y h : Fin d → ℝ) : psum y h d = y + h := by
  funext l
  simp [psum, l.isLt]
end PI.UnitaryGroupMassFormula.JCC.Ck
