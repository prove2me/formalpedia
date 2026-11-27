-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspShortVectors_proof_05f9e424b296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:41.557993+00:00
-- url     : https://prove2.me/submissions/5924bf8b-a737-4e98-8ee4-8d3b021410ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899

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
namespace GroundTheory.Heights₂.Heights
namespace CuspShortVectors
theorem _root_.solution (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPH : PeriodHermValue.Statement) :
    CuspShortVectors.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  refine ⟨Real.sqrt (min D.c (1 / M)), Real.sqrt_pos.mpr (lt_min D.c_pos (by positivity)), ?_⟩
  intro p hp hpU ℓ hℓ a n h
  obtain ⟨hY, hcY⟩ := hImPos D p.1 hpU ℓ hℓ
  unfold metricLength
  apply Real.sqrt_le_sqrt
  refine CuspShortVectors.value_ge _ hY hM hcY hPH T.r ?_ a n h
  intro k hk
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hMb p hp ℓ k k hk))
end CuspShortVectors
end GroundTheory.Heights₂.Heights
