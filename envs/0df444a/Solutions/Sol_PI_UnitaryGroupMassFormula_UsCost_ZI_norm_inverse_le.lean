-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.norm_inverse_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:41.354576+00:00
-- url     : https://prove2.me/submissions/1f623f1a-621d-4fbb-85ef-871706f3dded

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_inverse_eA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    ‖Ring.inverse (eA s Z)‖ ≤ ‖eA s‖ * ‖invF s Z‖ := by
  rw [inverse_eA s h]
  exact (eA s).le_opNorm _
end PI.UnitaryGroupMassFormula.UsCost.ZI
