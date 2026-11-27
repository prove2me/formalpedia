-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntGramSubLast_proof_bff89b1362e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:50.368842+00:00
-- url     : https://prove2.me/submissions/183dfda6-c0d3-45f1-a918-f8e8c161ff84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PIntGramSubLast

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
namespace IntGramSubLast
theorem _root_.solution : IntGramSubLast.Statement := by
  intro d k S M hM
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Fin.sum_univ_castSucc, hM, Int.cast_zero, zero_mul, mul_zero,
    add_zero]
end IntGramSubLast
end GroundTheory.Heights₂.Heights
