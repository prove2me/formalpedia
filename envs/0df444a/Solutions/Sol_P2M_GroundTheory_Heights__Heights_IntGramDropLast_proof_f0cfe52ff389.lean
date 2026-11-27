-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntGramDropLast_proof_f0cfe52ff389
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:16.104085+00:00
-- url     : https://prove2.me/submissions/a46d9e05-436b-41de-a82e-c06238f49d22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PIntGramDropLast

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
namespace IntGramDropLast
theorem _root_.solution : IntGramDropLast.Statement := by
  intro d k S N hN
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, id, Fin.sum_univ_castSucc, hN, Int.cast_zero, zero_mul, mul_zero,
    add_zero]
end IntGramDropLast
end GroundTheory.Heights₂.Heights
