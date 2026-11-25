-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegConeLimit_abs_fsLogReg_pointOf_le_cc18305be98c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:30.303675+00:00
-- url     : https://prove2.me/submissions/8671f873-c16f-4bfe-a1c8-51026cd06513

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegConeLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_dualNorm_pointOf_510e3d6db40f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_sum_mul_pointOf_le_681b629845aa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog
noncomputable section
open GroundTheory.Heights₂.Heights.RegConeLimit
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.RegConeLimit
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : ∑ j, u j * h.pointOf y j ≠ 0) :
    |fsLogReg h u ε (h.pointOf y)| ≤
      |fsLog h u (h.pointOf y)| + Real.log (h.norm u ^ 2 + 1) / 2 := by
  set a := ‖∑ j, u j * h.pointOf y j‖ with ha_def
  set r := ‖y‖ with hr_def
  have ha : 0 < a := norm_pos_iff.mpr hs
  have hCS : a ≤ h.norm u * r := norm_sum_mul_pointOf_le h u y
  have hN : 0 ≤ h.norm u := Real.sqrt_nonneg _
  have hr : 0 < r := by
    by_contra hle
    have h0 : r = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg y)
    rw [h0, mul_zero] at hCS
    linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have hreg : fsLogReg h u ε (h.pointOf y) = Real.log ((a ^ 2 + ε * r ^ 2) / r ^ 2) / 2 := by
    rw [fsLogReg, dualNorm_pointOf]
  have hlog : fsLog h u (h.pointOf y) = Real.log (a / r) := fsLog_pointOf h u y
  have hlow : fsLog h u (h.pointOf y) ≤ fsLogReg h u ε (h.pointOf y) := by
    rw [hreg, hlog]
    have h1 : (a / r) ^ 2 ≤ (a ^ 2 + ε * r ^ 2) / r ^ 2 := by
      rw [div_pow]; gcongr; nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hup : fsLogReg h u ε (h.pointOf y) ≤ Real.log (h.norm u ^ 2 + 1) / 2 := by
    rw [hreg]
    have h1 : (a ^ 2 + ε * r ^ 2) / r ^ 2 ≤ h.norm u ^ 2 + 1 := by
      rw [div_le_iff₀ hr2]
      have : a ^ 2 ≤ (h.norm u * r) ^ 2 := pow_le_pow_left₀ ha.le hCS 2
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    linarith
  have hK : 0 ≤ Real.log (h.norm u ^ 2 + 1) / 2 := by
    have : 0 ≤ Real.log (h.norm u ^ 2 + 1) := Real.log_nonneg (by nlinarith)
    linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le (fsLog h u (h.pointOf y))
    linarith
  · have := abs_nonneg (fsLog h u (h.pointOf y))
    linarith
end GroundTheory.Heights₂.Heights.RegConeLimit
