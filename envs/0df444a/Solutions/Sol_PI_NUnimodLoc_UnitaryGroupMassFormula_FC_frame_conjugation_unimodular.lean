-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conjugation_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:24:21.358932+00:00
-- url     : https://prove2.me/submissions/38044994-5ac8-45bd-b1d3-67170b58c5ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_qm_mul_pm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mul_qm
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_frame_conj_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution : FrameConj := by
  intro k r ε e f wf z0 z c hF hc hz
  exact ⟨Pm k r e f wf z0, Qm k r ε e f wf z0, qm_mul_pm hF, pm_mul_qm hF, fun g => frame_conj_iff hF hc hz g⟩
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
