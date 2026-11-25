-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_one_le_log_radius_6b216f4bf8bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:38.454818+00:00
-- url     : https://prove2.me/submissions/45d853a5-91c0-4aa8-a183-040c1d6a85f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exp_one_le_radius_f6ce9e042ee5

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
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ Real.log (D.radius z) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (exp_one_le_radius D hz)
end GroundTheory.Heights₂.Heights.MCBounds
