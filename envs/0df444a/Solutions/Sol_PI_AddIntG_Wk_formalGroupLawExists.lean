-- Prove2me | solution 1 for PI.AddIntG.Wk.formalGroupLawExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:58.675459+00:00
-- url     : https://prove2.me/submissions/0ae566fc-9c5a-4486-87d9-b1d246251a94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_Fch
import Theorems.Thm_PI_AddIntG_Wk_Fch_mem
import Theorems.Thm_PI_AddIntG_Wk_flog_Fch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution : KeyF := by
  intro p _ S W wq h1 h2 h3 h4 h6 h
  exact ⟨Fch W wq, Fch_mem h1 h2 h3 h4 h6 h, constantCoeff_Fch W wq, flog_Fch h⟩
end PI.AddIntG.Wk
