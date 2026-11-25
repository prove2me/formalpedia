-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.Gm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:46.466058+00:00
-- url     : https://prove2.me/submissions/5e188718-cacf-41a2-8192-4d1a6d57c6c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conj_mul_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (θ : AddCircle (2 * π)) : Matrix.of (Gm r θ) ∈ UWb 0 r := by
  show dgl r _ ∈ UWb 0 r
  exact dgl_mem ((conj_mul_iff _).2 (Circle.norm_coe _))
end PI.ExistsGaugeMeasureForEachRank.W
