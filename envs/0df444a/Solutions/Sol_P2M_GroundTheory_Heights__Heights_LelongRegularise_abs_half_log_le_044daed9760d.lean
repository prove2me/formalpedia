-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:58.947704+00:00
-- url     : https://prove2.me/submissions/ce68bce5-a495-4644-a2c2-167caf81376b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise
namespace GroundTheory.Heights₂.Heights.LelongRegularise
theorem _root_.solution {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (t ^ 2 + ε) / 2| ≤ |Real.log t| + |Real.log (2 * t)| := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hlo : Real.log t ≤ Real.log (t ^ 2 + ε) / 2 := by
    have : Real.log (t ^ 2) ≤ Real.log (t ^ 2 + ε) := Real.log_le_log ht2 (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hup : Real.log (t ^ 2 + ε) ≤ 2 * (|Real.log t| + |Real.log (2 * t)|) := by
    have h1 : Real.log (t ^ 2 + ε) ≤ Real.log (t ^ 2 + 1) := Real.log_le_log (by positivity) (by linarith)
    have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht.ne'
    rcases le_total t 1 with h | h
    · have : Real.log (t ^ 2 + 1) ≤ Real.log (2 ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := neg_abs_le (Real.log t)
      linarith
    · have : Real.log (t ^ 2 + 1) ≤ Real.log ((2 * t) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := abs_nonneg (Real.log t)
      linarith
  rw [abs_le]
  constructor
  · have a1 := neg_abs_le (Real.log t)
    have a2 := abs_nonneg (Real.log (2 * t))
    linarith
  · linarith
end GroundTheory.Heights₂.Heights.LelongRegularise
