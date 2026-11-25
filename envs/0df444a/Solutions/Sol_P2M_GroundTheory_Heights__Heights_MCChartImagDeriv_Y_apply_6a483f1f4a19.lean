-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:03.399069+00:00
-- url     : https://prove2.me/submissions/47408829-b6a2-4b41-92ed-cefa1e0a8f7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagDeriv

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartImagDeriv
namespace GroundTheory.Heights₂.Heights.MCChartImagDeriv
theorem _root_.solution (D : PeriodChartData) (z : Fin D.n → ℂ) (j l : Fin D.g) :
    D.Y z j l = (D.τ0 z j l).im + ∑ i, cuspTime D.a_le z i * D.B i j l := by
  simp [PeriodChartData.Y, chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
end GroundTheory.Heights₂.Heights.MCChartImagDeriv
