-- Prove2me | solution 1 for PI.CompDegEF.norm_natCast_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:10.870873+00:00
-- url     : https://prove2.me/submissions/0201a20d-8e67-4fe3-939f-9a6cbd2b8259

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] : 0 < ‖((l : ℕ) : Om l)‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast hl.out.pos)
end PI.CompDegEF
