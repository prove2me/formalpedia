-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_pairF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:08.807306+00:00
-- url     : https://prove2.me/submissions/6597f668-adad-45a3-a745-1ab894222a83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut

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
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (pairF k r z z') := by
  unfold pairF herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec
    ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))
end PI.RhsWLim.W
