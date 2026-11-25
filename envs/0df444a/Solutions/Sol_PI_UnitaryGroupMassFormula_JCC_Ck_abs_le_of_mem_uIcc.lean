-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.abs_le_of_mem_uIcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:48.0264+00:00
-- url     : https://prove2.me/submissions/6d1d557c-7c61-41ea-80a6-c742c6007a95

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
theorem _root_.solution {a s : ℝ} (hs : s ∈ Set.uIcc 0 a) : |s| ≤ |a| := by
  rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le.mpr ⟨by linarith [abs_nonneg a], h2.trans (le_abs_self a)⟩
  · exact abs_le.mpr ⟨(neg_abs_le a).trans h1, h2.trans (abs_nonneg a)⟩
end PI.UnitaryGroupMassFormula.JCC.Ck
