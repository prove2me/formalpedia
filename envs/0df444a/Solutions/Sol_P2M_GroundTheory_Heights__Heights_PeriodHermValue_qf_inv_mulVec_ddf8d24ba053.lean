-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodHermValue_qf_inv_mulVec_ddf8d24ba053
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:21.883237+00:00
-- url     : https://prove2.me/submissions/eaa8f2cf-7543-4d9c-9e77-e247bc3512b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodHermValue

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
open GroundTheory.Heights₂.Heights.PeriodHermValue
namespace GroundTheory.Heights₂.Heights.PeriodHermValue
theorem _root_.solution {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : IsUnit Y.det)
    (β : Fin g → ℝ) : MCSchur.qf Y⁻¹ (Y *ᵥ β) = MCSchur.qf Y β := by
  unfold MCSchur.qf
  rw [mulVec_mulVec, nonsing_inv_mul Y hY, one_mulVec, dotProduct_comm]
end GroundTheory.Heights₂.Heights.PeriodHermValue
