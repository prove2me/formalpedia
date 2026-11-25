-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:26.190567+00:00
-- url     : https://prove2.me/submissions/a491ab31-763c-420b-93bb-60cb8dcd2df0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct

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
open GroundTheory.Heights₂.Heights.GramPivotProduct
namespace GroundTheory.Heights₂.Heights.GramPivotProduct
theorem _root_.solution {d k : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : Sᵀ = S)
    (N : Matrix (Fin d) (Fin k) ℤ) : (intGram S N)ᵀ = intGram S N := by
  simp only [intGram, transpose_mul, transpose_transpose, hS, Matrix.mul_assoc]
end GroundTheory.Heights₂.Heights.GramPivotProduct
