-- Prove2me | solution 1 for PI.PrimesDyadicRS.W.floor_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:24.201146+00:00
-- url     : https://prove2.me/submissions/726f6632-55dd-47a2-ac34-8a0cabe86538

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_FloorHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.W
namespace PI.PrimesDyadicRS.W
theorem _root_.solution (y : ℝ) : ⌊y⌋₊ = ⌊2 * y⌋₊ / 2 := by
  have e : (2 * y) / ((2 : ℕ) : ℝ) = y := by push_cast; ring
  calc ⌊y⌋₊ = ⌊(2 * y) / ((2 : ℕ) : ℝ)⌋₊ := by rw [e]
    _ = ⌊2 * y⌋₊ / 2 := Nat.floor_div_natCast _ _
end PI.PrimesDyadicRS.W
