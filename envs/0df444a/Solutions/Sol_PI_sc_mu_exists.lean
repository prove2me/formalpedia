-- Prove2me | solution 1 for PI.sc_mu_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:06.003837+00:00
-- url     : https://prove2.me/submissions/51e6674f-47d3-4e5d-8540-c0f6ca9fb81d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_TargetOfInstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAll
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScMuExists
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_place_decomposition_instance
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_target_of_instDecomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
namespace PI
theorem _root_.solution : PI.ScMuExists.Target :=
  PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance
end PI
