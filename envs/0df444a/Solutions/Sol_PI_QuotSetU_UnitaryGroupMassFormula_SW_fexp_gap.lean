-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.fexp_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:22.790497+00:00
-- url     : https://prove2.me/submissions/eb086591-fd98-4da5-b851-4086f9f845a0

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
theorem _root_.solution {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hW : ¬ (inW k r i ∧ inW k r j)) :
    1 ≤ fexp k r i - fexp k r j := by
  simp only [inW] at hW
  simp only [fexp]
  split_ifs <;> omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
