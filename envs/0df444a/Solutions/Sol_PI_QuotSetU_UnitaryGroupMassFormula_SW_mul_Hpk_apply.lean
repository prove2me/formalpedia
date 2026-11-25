-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:28.035021+00:00
-- url     : https://prove2.me/submissions/110412f9-044e-4ddf-a0e8-4f0b963cace9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply

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
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  have hc : ∀ l, (j = piI k r l) ↔ (l = piI k r j) :=
    fun l => ⟨fun h => by rw [h, piI_piI], fun h => by rw [h, piI_piI]⟩
  simp only [Matrix.mul_apply, Hpk_apply, hc, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, epsI_piI]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
