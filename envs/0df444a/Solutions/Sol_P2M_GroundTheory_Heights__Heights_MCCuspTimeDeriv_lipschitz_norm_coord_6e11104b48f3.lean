-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_lipschitz_norm_coord_6e11104b48f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:05.28146+00:00
-- url     : https://prove2.me/submissions/4cd232e4-3530-4276-aac6-6f9e0afb246c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspTimeDeriv

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
open GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
namespace GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
theorem _root_.solution {n : ℕ} (c : Fin n) :
    LipschitzWith 1 (fun w : Fin n → ℂ => ‖w c‖) := by
  have h := (lipschitzWith_one_norm (E := ℂ)).comp (LipschitzWith.eval (α := fun _ : Fin n => ℂ) c)
  rw [mul_one] at h
  exact h
end GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
