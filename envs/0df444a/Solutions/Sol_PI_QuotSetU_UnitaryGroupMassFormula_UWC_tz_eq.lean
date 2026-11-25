-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.tz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:27.745812+00:00
-- url     : https://prove2.me/submissions/e95c72ba-ba90-4b29-a640-fafbb188dbbd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_star_dotProduct_Hpk_mulVec_eq_sum_sub
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_star_mul_self_eq

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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    Tz k r z = ‖z (lI k r)‖ ^ 2 - ∑ i ∈ Wp k r, ‖z i‖ ^ 2 := by
  have hv : ∀ i, ¬ inW k r i → z i = 0 := fun i hi => hz i (by unfold inW at hi; omega)
  unfold Tz herm
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub z z hv]
  simp only [star_mul_self_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
