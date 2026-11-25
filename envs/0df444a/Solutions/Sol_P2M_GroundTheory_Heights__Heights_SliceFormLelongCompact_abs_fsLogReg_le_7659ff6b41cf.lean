-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:56.124267+00:00
-- url     : https://prove2.me/submissions/d25279a1-e7fb-43c7-9bf1-adec485dd376

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d


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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution (h : HermNorm n) (u x : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : linEval u x ≠ 0) (hx : 0 < h.dualNorm x) :
    |fsLogReg h u ε x| ≤ 2 * |Real.log ‖linEval u x‖| + (2 * |Real.log (h.dualNorm x)| + 1) := by
  have ht : 0 < ‖linEval u x‖ := norm_pos_iff.2 hu
  have he : fsLogReg h u ε x = Real.log ((‖linEval u x‖ / h.dualNorm x) ^ 2 + ε) / 2 := by
    unfold fsLogReg linEval
    congr 2
    field_simp
  rw [he]
  refine (LelongRegularise.abs_half_log_le (div_pos ht hx) hε hε1).trans ?_
  rw [Real.log_mul two_ne_zero (div_pos ht hx).ne', Real.log_div ht.ne' hx.ne']
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have h2' : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have a1 := abs_sub (Real.log ‖linEval u x‖) (Real.log (h.dualNorm x))
  have a2 := abs_add_le (Real.log 2) (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))
  rw [abs_of_nonneg h2'] at a2
  linarith
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
