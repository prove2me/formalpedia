-- Prove2me | solution 1 for PI.RhsWLim.W.RI.herm_wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:19.685646+00:00
-- url     : https://prove2.me/submissions/2cfd41ce-681e-4aa9-a04b-54de0e5b8bf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
import Theorems.Thm_PI_RhsWLim_W_MB_Hpk_Em
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_em_dot
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_inWb_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution {x w : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hw : inWb k r w) :
    herm (Hpk k r) x w = herm (Hb k) (wbPart k r x) (wbPart k r w) := by
  conv_lhs => rw [← inWb_eq hx, ← inWb_eq hw]
  unfold herm
  rw [Matrix.mulVec_mulVec, MB.Hpk_Em, ← Matrix.mulVec_mulVec, em_dot]
end PI.RhsWLim.W.RI
