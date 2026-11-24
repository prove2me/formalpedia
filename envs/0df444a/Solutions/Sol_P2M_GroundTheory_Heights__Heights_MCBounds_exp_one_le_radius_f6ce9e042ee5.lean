-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:09.256579+00:00
-- url     : https://prove2.me/submissions/c5a42044-7c2a-489c-8b92-ebfa98538cda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) : Real.exp 1 ≤ D.radius z := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => log_inv_sq_nonneg (cusp_norm_lt D hz j)
  simp only [PeriodChartData.radius, chartRadius]
  linarith
end GroundTheory.Heights₂.Heights.MCBounds
