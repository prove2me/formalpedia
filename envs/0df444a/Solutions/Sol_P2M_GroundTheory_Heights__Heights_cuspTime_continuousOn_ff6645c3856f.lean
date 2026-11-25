-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:17.189854+00:00
-- url     : https://prove2.me/submissions/141398ec-16ae-4112-a055-8fda960fba84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagContinuous

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
theorem _root_.solution {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) (j : Fin a) :
    ContinuousOn (fun z => cuspTime h z j) (puncturedChart h U) := by
  have hc : Continuous (fun z : Fin n → ℂ => cuspCoord h z j) := continuous_apply _
  have hne : ∀ z ∈ puncturedChart h U, ‖cuspCoord h z j‖ ≠ 0 := fun z hz =>
    norm_ne_zero_iff.mpr (hz.2 j)
  have hinv : ContinuousOn (fun z => ‖cuspCoord h z j‖⁻¹) (puncturedChart h U) :=
    hc.norm.continuousOn.inv₀ hne
  exact continuousOn_const.mul (hinv.log fun z hz => inv_ne_zero (hne z hz))
end GroundTheory.Heights₂.Heights
