-- Prove2me | solution 1 for PI.EF.localAbstract_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:01.047118+00:00
-- url     : https://prove2.me/submissions/b522774c-6aec-45e6-8929-db603091e50c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalProofs
import Theorems.Thm_PI_EF_Loc_locC_pos
import Theorems.Thm_PI_EF_Loc_local_abstract


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF
namespace PI.EF
theorem _root_.solution (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩
end PI.EF
