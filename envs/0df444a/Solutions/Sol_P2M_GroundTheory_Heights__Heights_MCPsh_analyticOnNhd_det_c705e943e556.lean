-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:12.884803+00:00
-- url     : https://prove2.me/submissions/88caf201-4109-4825-ac10-d14f3542caf8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {s : Set ℂ} {M : ℂ → Matrix κ κ ℂ}
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun ζ => M ζ i j) s) :
    AnalyticOnNhd ℂ (fun ζ => (M ζ).det) s := by
  have : (fun ζ => (M ζ).det) =
      fun ζ => ∑ σ : Equiv.Perm κ, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M ζ (σ i) i := by
    funext ζ
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  intro z hz
  refine Finset.univ.analyticAt_fun_sum fun σ _ => ?_
  exact analyticAt_const.mul (Finset.univ.analyticAt_fun_prod fun i _ => hM _ _ z hz)
end GroundTheory.Heights₂.Heights.MCPsh
