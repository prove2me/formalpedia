-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DB.U_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:13.899222+00:00
-- url     : https://prove2.me/submissions/066c9c4c-6042-489f-96b1-436eb548953a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block2_det_upper_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block2_det_upper_triangular


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
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost.DB
theorem _root_.solution {p s : ℕ} (b : Fin p → Fin s → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
      blk2 1 (Matrix.of b) 0 1 = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [P.Ux4.block2_det_upper_triangular]
  simp
end PI.UnitaryGroupMassFormula.UsCost.DB
