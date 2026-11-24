-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:32.46525+00:00
-- url     : https://prove2.me/submissions/8b29b41f-606d-464e-b275-3adb89aef276

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_norm_coord_lt_a42ac747c733

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
    (hz : z ∈ puncturedChart h (ball (0 : Fin n → ℂ) 1)) : logLift a z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.isLt
    have h0 : z (Fin.castLE h i) ≠ 0 := hz.2 i
    simp only [logLift, if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr h0) (norm_coord_lt hz.1 _)
  · simp only [logLift, if_neg (not_lt.mpr hk)]
    exact norm_coord_lt hz.1 k
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
