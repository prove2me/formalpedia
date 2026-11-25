-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:11.153703+00:00
-- url     : https://prove2.me/submissions/ae8604f5-fa8a-497f-be9c-de570439380d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolURatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair

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
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => ((fun i : Fin k => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i))),
      (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) := by
  have hc : Continuous fun x : Mt k r => Matrix.of x *ᵥ z' :=
    Continuous.matrix_mulVec (continuous_id (X := Mat k r)) continuous_const
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)
end PI.RhsWLim.W
