-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.exp_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:53.796515+00:00
-- url     : https://prove2.me/submissions/aec5568b-999e-4ce2-8c9b-0fa735e7556e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (z : ℂ) : NormedSpace.exp (dz r z) = dgl r (Complex.exp z) := by
  rw [dz, Matrix.exp_diagonal, dgl]
  congr 1
  funext i
  rw [Pi.coe_exp]
  by_cases h : i = cI r
  · subst h
    simp [← Complex.exp_eq_exp_ℂ]
  · simp [h]
end PI.ExistsGaugeMeasureForEachRank.W
