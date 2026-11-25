-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.tr_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:20.651688+00:00
-- url     : https://prove2.me/submissions/aacecd65-e6c2-4efe-b2f2-3d0f206839ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution (m : ℕ) : Continuous (tr m) :=
  continuous_induced_rng.2 (continuous_subtype_val.matrix_transpose)
end PI.UMultOne.UnitaryGroupMassFormula
