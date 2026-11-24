-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:30.306249+00:00
-- url     : https://prove2.me/submissions/dde206b9-edaf-40f8-a703-a4b1bcb441e4

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
theorem _root_.solution {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ D.radius z := by
  have := exp_one_le_radius D hz
  have := Real.add_one_le_exp (1 : ℝ)
  linarith
end GroundTheory.Heights₂.Heights.MCBounds
