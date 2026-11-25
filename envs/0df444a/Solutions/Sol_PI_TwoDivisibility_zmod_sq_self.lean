-- Prove2me | solution 1 for PI.TwoDivisibility.zmod_sq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:40.258507+00:00
-- url     : https://prove2.me/submissions/200523f8-4162-4f46-a8bd-fdb894b50dc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TwoDivisibility
namespace PI.TwoDivisibility
theorem _root_.solution : ∀ a : ZMod 2, a * a = a := by decide
end PI.TwoDivisibility
