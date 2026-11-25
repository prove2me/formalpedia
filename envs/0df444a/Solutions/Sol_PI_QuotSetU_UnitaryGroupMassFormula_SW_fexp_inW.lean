-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.fexp_inW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:28.119285+00:00
-- url     : https://prove2.me/submissions/91d4bea9-3301-4808-92ce-0c80d3e4d5f7

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
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : inW k r i) : fexp k r i = 0 := by
  obtain ⟨h1, h2⟩ := hi
  simp only [fexp]
  split_ifs <;> omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
