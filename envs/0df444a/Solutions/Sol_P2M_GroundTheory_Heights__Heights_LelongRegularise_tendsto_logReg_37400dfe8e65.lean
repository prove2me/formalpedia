-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:39.49255+00:00
-- url     : https://prove2.me/submissions/cd75a319-3a34-4d98-aa5c-ec13e303fbfb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc


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
theorem _root_.solution {n : ℕ} (u x : Fin n → ℂ) (hx : linEval u x ≠ 0) :
    Tendsto (fun ε => logReg u ε x) (𝓝[>] 0) (𝓝 (Real.log ‖linEval u x‖)) := by
  rw [← logReg_zero]
  have hc : ContinuousAt (fun ε => logReg u ε x) 0 := by
    unfold logReg
    refine ContinuousAt.div_const (ContinuousAt.log (continuousAt_const.add continuousAt_id) ?_) _
    simp [hx]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds
end GroundTheory.Heights₂.Heights.LelongRegularise
