-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.dS_mul_dS_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:35.553863+00:00
-- url     : https://prove2.me/submissions/1d77f08b-fc8c-4ae2-a3b9-a1d673c24e64

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
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) : dS k r s * dS k r s⁻¹ = 1 := by
  rw [dS, dS, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← mul_zpow, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs), _root_.one_zpow]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
