-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotLast_proof_5acde1d3fec9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:34.511874+00:00
-- url     : https://prove2.me/submissions/550b7a40-3b26-4b79-b641-9a21bb6dbbf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262


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
namespace PivotLast
theorem _root_.solution (hPI : PivotInvDiag.Statement) : PivotLast.Statement := by
  intro d S hS x
  have h1 := MCCusp.sq_le_inv_diag_mul_qf hS x (Fin.last d)
  have h2 := hPI d S hS
  have hpos : 0 < S⁻¹ (Fin.last d) (Fin.last d) := hS.inv.diag_pos
  have hp : 0 < pivot S d := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
    linarith
  calc x (Fin.last d) ^ 2 * pivot S d
      ≤ (S⁻¹ (Fin.last d) (Fin.last d) * MCSchur.qf S x) * pivot S d :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = MCSchur.qf S x * (S⁻¹ (Fin.last d) (Fin.last d) * pivot S d) := by ring
    _ = MCSchur.qf S x := by rw [h2, mul_one]
end PivotLast
end GroundTheory.Heights₂.Heights
