-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:02.475438+00:00
-- url     : https://prove2.me/submissions/ebd1f7d9-11e5-466e-bf65-632b67d68bc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605


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
theorem _root_.solution {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ}
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : 1 ≤ chartRadius h z := by
  have : 0 ≤ ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => log_inv_sq_nonneg (norm_coord_lt hz.1 _)
  unfold chartRadius
  linarith [Real.add_one_le_exp (1 : ℝ)]
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
