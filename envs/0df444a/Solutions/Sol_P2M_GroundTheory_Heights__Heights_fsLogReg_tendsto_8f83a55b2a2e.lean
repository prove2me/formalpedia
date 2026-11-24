-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fsLogReg_tendsto_8f83a55b2a2e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.331906+00:00
-- url     : https://prove2.me/submissions/d79f9805-5881-4935-960a-456ac256834a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg

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
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (u y : Fin n → ℂ) (hy : 0 < h.dualNorm y)
    (hu : ∑ j, u j * y j ≠ 0) :
    Tendsto (fun ε => fsLogReg h u ε y) (𝓝 0) (𝓝 (fsLog h u y)) := by
  have hc : (0 : ℝ) < h.dualNorm y ^ 2 := by positivity
  have hs : (0 : ℝ) < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hu
  have hcont : ContinuousAt (fun ε : ℝ =>
      Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2) 0 := by
    refine ContinuousAt.div_const (ContinuousAt.log ?_ ?_) _
    · fun_prop
    · simp only [zero_mul, add_zero]
      positivity
  have := hcont.tendsto
  simp only [zero_mul, add_zero] at this
  unfold fsLogReg
  convert this using 2
  rw [fsLog, ← div_pow, Real.log_pow]
  push_cast
  ring
end GroundTheory.Heights₂.Heights
