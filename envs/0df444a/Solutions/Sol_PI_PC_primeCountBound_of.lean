-- Prove2me | solution 1 for PI.PC.primeCountBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:41.465906+00:00
-- url     : https://prove2.me/submissions/8535d40a-33e5-465e-9fe3-664728495b6b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimeCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution (x₀ : ℝ) (hL : PCLarge x₀) (hS : PCSmall x₀) : PI.PrimeCountBound := by
  intro y hy
  by_cases h : x₀ ≤ y
  · exact hL y h
  · exact hS y hy (lt_of_not_ge h)
end PI.PC
