-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.vol_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:13.760797+00:00
-- url     : https://prove2.me/submissions/9f87cb25-ffa9-4da0-b8e3-1f8501ec54d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_finrank_lie

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
theorem _root_.solution {ρ : ℝ} (h0 : 0 ≤ ρ) :
    volume (Metric.ball (0 : lieE (UWb 0 r)) ρ) = ENNReal.ofReal (2 * ρ) := by
  have : Nontrivial (lieE (UWb 0 r)) := Module.nontrivial_of_finrank_eq_succ finrank_lie
  rw [InnerProductSpace.volume_ball, finrank_lie]
  simp only [pow_one, Nat.cast_one]
  have hg : Real.Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have hs : √π / (√π / 2) = 2 := by
    have : √π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
    field_simp
  rw [hg, hs, ← ENNReal.ofReal_mul h0, mul_comm]
end PI.ExistsGaugeMeasureForEachRank.W
