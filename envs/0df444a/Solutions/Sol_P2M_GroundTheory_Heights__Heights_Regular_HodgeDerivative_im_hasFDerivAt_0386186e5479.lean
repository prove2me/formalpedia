-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_im_hasFDerivAt_0386186e5479
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:58.023306+00:00
-- url     : https://prove2.me/submissions/b3d34fe2-33de-4da5-9996-67d2616d2de7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x ∧
      ‖Complex.imCLM.comp (fderiv ℝ f x)‖ ≤ ‖fderiv ℝ f x‖ := by
  refine ⟨Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans ((fderiv ℝ f x).le_opNorm v)
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
