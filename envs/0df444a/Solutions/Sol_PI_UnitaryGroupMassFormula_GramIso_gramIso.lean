-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramIso.gramIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:46.806949+00:00
-- url     : https://prove2.me/submissions/5a393f2f-2c3a-411a-ae9c-7f5673ffdf36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_be_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramIso
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.GramIso
theorem _root_.solution : PI.FglGram.GramIso := by
  intro p _ l ex ph hD κ _ r b hb
  simp only [GramRhs, hb, Prod.fst_zero, map_zero, zero_mul, Finset.sum_const_zero, zero_add,
    be_zero_left l ex ph hD]
end PI.UnitaryGroupMassFormula.GramIso
