-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:35.855498+00:00
-- url     : https://prove2.me/submissions/1039c093-55ee-4732-9dab-d243e2977063

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (s : ℝ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (dS k r s * g * dS k r s⁻¹) i j = (s : ℂ) ^ (fexp k r i) * g i j * ((s⁻¹ : ℝ) : ℂ) ^ (fexp k r j) := by
  rw [dS, dS, Matrix.mul_diagonal, Matrix.diagonal_mul]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
