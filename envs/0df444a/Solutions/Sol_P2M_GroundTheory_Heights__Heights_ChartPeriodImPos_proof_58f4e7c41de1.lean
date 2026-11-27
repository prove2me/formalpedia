-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartPeriodImPos_proof_58f4e7c41de1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:41.372225+00:00
-- url     : https://prove2.me/submissions/1f1283a6-7338-4aad-a185-6a13316ec0f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartPeriodImPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd


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
namespace ChartPeriodImPos
theorem _root_.solution : ChartPeriodImPos.Statement := by
  intro D z hz ℓ hℓ
  rw [MCPeriod.period_im D z ℓ hℓ]
  have hY : (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef := D.Y_ge z hz
  refine ⟨?_, ?_⟩
  · have e : D.Y z = (D.Y z - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)) +
        D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) := by abel
    rw [e]
    exact Matrix.PosDef.posSemidef_add hY (PosDef.one.smul D.c_pos)
  · intro x
    have h := hY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at h
    have hx : x ⬝ᵥ x = ∑ k, x k ^ 2 := by
      simp only [dotProduct, sq]
    rw [hx] at h
    rw [MCSchur.qf]
    linarith
end ChartPeriodImPos
end GroundTheory.Heights₂.Heights
