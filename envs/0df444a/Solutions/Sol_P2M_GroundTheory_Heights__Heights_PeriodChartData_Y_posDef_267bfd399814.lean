-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodChartData_Y_posDef_267bfd399814
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:27.704365+00:00
-- url     : https://prove2.me/submissions/2f087d0b-3e2d-439f-a990-053abd337589

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartPotentialPsh

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
open Matrix Metric Real MCPsh
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PeriodChartData
theorem _root_.solution (D : PeriodChartData) {z : Fin D.n → ℂ} (hz : z ∈ D.Ustar) :
    (D.Y z).PosDef := by
  have h := Matrix.PosDef.posSemidef_add (D.Y_ge z hz) (PosDef.one.smul D.c_pos)
  simpa [PeriodChartData.Y] using h
end PeriodChartData
end GroundTheory.Heights₂.Heights
