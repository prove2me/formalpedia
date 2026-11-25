-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:40.25444+00:00
-- url     : https://prove2.me/submissions/27c4daf1-d40c-45d3-ac00-6c32678ebe59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramContinuous

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
open Matrix Metric MCPsh
open scoped MatrixOrder ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.MCPsh
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {X : Type} [TopologicalSpace X] {s : Set X} {g : ℕ}
    {Y : X → Matrix (Fin g) (Fin g) ℝ} (hY : ContinuousOn Y s) (hpd : ∀ x ∈ s, (Y x).PosDef) :
    ContinuousOn (fun x => (Y x)⁻¹) s := by
  intro x hx
  have hdet : (Y x).det ≠ 0 := (hpd x hx).det_pos.ne'
  have hinvR : ContinuousAt (Ring.inverse : ℝ → ℝ) (Y x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hinvAt : ContinuousAt (Inv.inv : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℝ)
      (Y x) := continuousAt_matrix_inv _ hinvR
  exact hinvAt.comp_continuousWithinAt (hY x hx)
end GroundTheory.Heights₂.Heights.MCPsh
