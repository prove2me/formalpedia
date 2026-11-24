-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:09.514713+00:00
-- url     : https://prove2.me/submissions/495ee5f4-1d27-489c-80e7-0815f036b496

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logReg u ε) := by
  unfold logReg
  refine ContDiff.div_const (ContDiff.log (((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).add
    contDiff_const) fun x => ?_) _
  have : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
  simp only [Function.comp_apply]
  linarith
end GroundTheory.Heights₂.Heights
