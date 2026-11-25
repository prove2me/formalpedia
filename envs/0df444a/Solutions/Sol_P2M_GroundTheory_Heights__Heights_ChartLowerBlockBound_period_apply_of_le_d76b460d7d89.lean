-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:02.780143+00:00
-- url     : https://prove2.me/submissions/47dc5ac5-5cca-4a02-ae97-466941aff5c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartLowerHeightsound

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
open GroundTheory.Heights₂.Heights.ChartLowerBlockBound
namespace GroundTheory.Heights₂.Heights.ChartLowerBlockBound
theorem _root_.solution (D : PeriodChartData) (T : ToricBlock D) (z : Fin D.n → ℂ)
    (ℓ : Fin D.a → ℂ) (i l : Fin D.g) (h : T.r ≤ i.val) :
    D.period z ℓ i l = D.τ0 z i l := by
  simp [PeriodChartData.period, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.map_apply, T.support _ i l (Or.inl h)]
end GroundTheory.Heights₂.Heights.ChartLowerBlockBound
