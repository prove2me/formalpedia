-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogDetGramContinuous_proof_ef2590af84cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:13.419855+00:00
-- url     : https://prove2.me/submissions/7aec6012-68cd-4b4c-8649-941c11ff0a89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramContinuous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_continuousOn_inv_of_posDef_a099a701d7dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_continuous_gram_a2087d2140df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329


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
namespace GroundTheory.Heights₂.Heights
namespace LogDetGramContinuous
theorem _root_.solution : LogDetGramContinuous.Statement := by
  intro X _ s g rk Y F hY hF hpd hr
  have hYinv := continuousOn_inv_of_posDef hY hpd
  have hΦ : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      (p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1).det.re) :=
    Complex.continuous_re.comp (continuous_gram g rk).matrix_det
  have hG := hΦ.comp_continuousOn (hF.prodMk hYinv)
  simp only [Function.comp_def] at hG
  show ContinuousOn (fun x => Real.log ((F x)ᴴ * ((Y x)⁻¹).map (fun x : ℝ => (x : ℂ)) * F x).det.re) s
  refine hG.log fun x hx => ?_
  have h := MCDet.re_det_pos (gram_posDef (hpd x hx) (hr x hx))
  rw [RCLike.re_to_complex] at h
  exact h.ne'
end LogDetGramContinuous
end GroundTheory.Heights₂.Heights
