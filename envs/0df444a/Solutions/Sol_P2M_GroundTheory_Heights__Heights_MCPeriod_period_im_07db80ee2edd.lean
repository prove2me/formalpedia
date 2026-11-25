-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:01.270968+00:00
-- url     : https://prove2.me/submissions/28b6dcaa-b116-4211-aabb-44ed537609d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPeriod_cfac_im_8dde78dbb036

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPeriod
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPeriod
theorem _root_.solution (D : PeriodChartData) (z : Fin D.n → ℂ) (l : Fin D.a → ℂ)
    (h : ∀ j, Complex.exp (l j) = cuspCoord D.a_le z j) :
    (D.period z l).map Complex.im = D.Y z := by
  ext k m
  simp only [PeriodChartData.period, PeriodChartData.Y, chartImag, Matrix.map_apply,
    Matrix.add_apply, Matrix.sum_apply, Complex.add_im, Complex.im_sum, Matrix.smul_apply,
    smul_eq_mul, cuspTime]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.im_mul_ofReal, cfac_im, h j]
end GroundTheory.Heights₂.Heights.MCPeriod
