-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_gram_posDef_60007937f6e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:18.22724+00:00
-- url     : https://prove2.me/submissions/f9581287-1491-4362-904e-c2a2329dea8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramContinuous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_inv_7b358c22ed20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192


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
theorem _root_.solution {g rk : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {F : Matrix (Fin g) (Fin rk) ℂ}
    (hY : Y.PosDef) (hF : F.rank = rk) :
    (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).PosDef := by
  have hinj : Function.Injective F.mulVec := mulVec_injective_of_rank (by rw [hF, Fintype.card_fin])
  have := (cx_posDef hY).inv.conjTranspose_mul_mul_same hinj
  rwa [cx_inv ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)] at this
end GroundTheory.Heights₂.Heights.MCPsh
