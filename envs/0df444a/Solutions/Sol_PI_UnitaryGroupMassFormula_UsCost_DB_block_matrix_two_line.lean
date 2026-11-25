-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DB.block_matrix_two_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:55.720146+00:00
-- url     : https://prove2.me/submissions/06117574-7a6b-4d51-8131-efd3a7f2eb41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_symmetricScalarBlockMatrix_one_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
namespace PI.UnitaryGroupMassFormula.UsCost.DB
theorem _root_.solution {p s : ℕ} (t : ℝ) (A : Matrix (Fin s) (Fin s) ℂ) :
    blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 + t • A) = 1 + t • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 A := by
  rw [← symmetricScalarBlockMatrix_one_zero]
  ext i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;> simp
end PI.UnitaryGroupMassFormula.UsCost.DB
