-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.Gm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:56.485882+00:00
-- url     : https://prove2.me/submissions/e30d2040-80cc-46de-8087-f6d7598ec82b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_mul


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
theorem _root_.solution (a b : AddCircle (2 * π)) :
    Gm r (a + b) = lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) := by
  have : lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) =
      dgl r ((AddCircle.toCircle a : Circle) : ℂ) * dgl r ((AddCircle.toCircle b : Circle) : ℂ) := rfl
  have h2 : ((AddCircle.toCircle (a + b) : Circle) : ℂ) =
      ((AddCircle.toCircle a : Circle) : ℂ) * ((AddCircle.toCircle b : Circle) : ℂ) := by
    rw [AddCircle.toCircle_add, Circle.coe_mul]
  rw [this, dgl_mul]
  unfold Gm
  rw [h2]
end PI.ExistsGaugeMeasureForEachRank.W
