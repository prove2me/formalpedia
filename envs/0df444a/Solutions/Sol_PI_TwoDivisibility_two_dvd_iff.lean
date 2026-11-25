-- Prove2me | solution 1 for PI.TwoDivisibility.two_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:49.230299+00:00
-- url     : https://prove2.me/submissions/496bfe6e-5cae-426f-a073-d6281fe9f0c4

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
theorem _root_.solution (p : ℤ) : (2 : ℤ) ∣ p ↔ ((p : ZMod 2) = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
end PI.TwoDivisibility
