-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:32.476397+00:00
-- url     : https://prove2.me/submissions/48e4be26-3f7b-4c26-af90-876f91a1044c

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
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    cuspTime D.a_le z j ≤ D.radius z := by
  have hlt := cusp_norm_lt D hz j
  have hL : 0 ≤ -Real.log ‖cuspCoord D.a_le z j‖ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hlt.le)
  have hterm : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ = 2 * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hsum : Real.log (‖cuspCoord D.a_le z j‖ ^ 2)⁻¹ ≤
      ∑ i, Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹ :=
    Finset.single_le_sum (f := fun i => Real.log (‖cuspCoord D.a_le z i‖ ^ 2)⁻¹)
      (fun i _ => log_inv_sq_nonneg (cusp_norm_lt D hz i)) (Finset.mem_univ j)
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have he := Real.exp_pos 1
  have h1 : cuspTime D.a_le z j = (2 * Real.pi)⁻¹ * -Real.log ‖cuspCoord D.a_le z j‖ := by
    rw [cuspTime, Real.log_inv]
  have h2 := mul_le_mul_of_nonneg_right hpi hL
  rw [h1]
  simp only [PeriodChartData.radius, chartRadius]
  linarith
end GroundTheory.Heights₂.Heights.MCBounds
