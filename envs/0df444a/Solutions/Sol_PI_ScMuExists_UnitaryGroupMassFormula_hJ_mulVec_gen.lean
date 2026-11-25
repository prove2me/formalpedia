-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.hJ_mulVec_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:36.053077+00:00
-- url     : https://prove2.me/submissions/fc00284d-ead7-4ba2-a25a-575e02e01a59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) :
    hJ ε (A *ᵥ u) (A *ᵥ w) = star u ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ w) := by
  simp only [hJ, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_assoc]
end PI.ScMuExists.UnitaryGroupMassFormula
