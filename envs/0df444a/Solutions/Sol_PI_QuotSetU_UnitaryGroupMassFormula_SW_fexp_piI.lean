-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.fexp_piI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:13.482061+00:00
-- url     : https://prove2.me/submissions/28aef0e5-c80c-4d1b-a1ba-6938ffcd618f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val


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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : fexp k r (piI k r i) = - fexp k r i := by
  have hi := i.isLt
  have hv := piI_val (k := k) (r := r) i
  simp only [fexp]
  split_ifs at hv ⊢ <;> omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
