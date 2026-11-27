-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MatrixDetDeriv_hypotheses_met_d0008cb64df5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:30.408441+00:00
-- url     : https://prove2.me/submissions/319a7431-0f03-42c4-aefe-df363914ebb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds

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
namespace MatrixDetDeriv
theorem _root_.solution :
    ∀ j l : Fin 2, DifferentiableAt ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0 ∧
      ‖(fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 j l‖ ≤ 1 ∧
      ‖fderiv ℝ (fun q : ℝ => (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q j l) 0‖ ≤ 0 := by
  intro j l
  refine ⟨differentiableAt_const _, ?_, by simp⟩
  by_cases h : j = l <;> simp [Matrix.one_apply, h]
end MatrixDetDeriv
end GroundTheory.Heights₂.Heights
