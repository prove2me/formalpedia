-- Prove2me | solution 1 for PI.TwoDivisibility.zmod_pick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:36.338114+00:00
-- url     : https://prove2.me/submissions/d2f69fb0-1bcf-4409-ad4e-b22a5467e9c6

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
theorem _root_.solution : ∀ a b c e : ZMod 2, a + e = 1 → b * c = 0 →
    ∃ m n : ZMod 2, (m * a + n * c ≠ 0 ∨ m * b + n * e ≠ 0) ∧
      (m - (m * a + n * c) ≠ 0 ∨ n - (m * b + n * e) ≠ 0) := by
  decide
end PI.TwoDivisibility
