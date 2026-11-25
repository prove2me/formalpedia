-- Prove2me | solution 1 for PI.RhsWLim.W.GE.splitHermForm_apply_firstMiddle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:33.627275+00:00
-- url     : https://prove2.me/submissions/b2ebb0e4-1b25-4e3e-a10a-07bb77c0d70e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_GE_firstMiddle_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.GE
variable {k r : ℕ}
namespace PI.RhsWLim.W.GE
theorem _root_.solution (i : Fin (2 * r + k + 1)) (hi : i ≠ p0 k r) : Hpk k r i (p0 k r) = 0 := by
  have hv := firstMiddle_val (k := k) (r := r)
  simp only [Hpk]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)
end PI.RhsWLim.W.GE
