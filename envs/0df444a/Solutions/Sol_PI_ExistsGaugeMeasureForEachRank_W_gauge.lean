-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.gauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:55.738962+00:00
-- url     : https://prove2.me/submissions/84bc2db9-e3b4-40b4-a6fd-c5d2e5d8e77b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Gm_injective
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_me_Gm
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_isHaar
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_expBall_eq
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_vol_arc
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_vol_ball

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
theorem _root_.solution (r : ℕ) : IsGaugeOn (UWb 0 r) (μG r) := by
  refine ⟨isHaar, ?_⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ρ hρ
  rw [μG, me_Gm.map_apply, expBall_eq, Gm_injective.preimage_image, vol_arc hρ.2.le,
    vol_ball hρ.1.le, div_self]
  rw [ENNReal.toReal_ofReal (by linarith [hρ.1])]
  linarith [hρ.1]
end PI.ExistsGaugeMeasureForEachRank.W
