-- Prove2me | solution 1 for PI.PC.chLower_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:22.71688+00:00
-- url     : https://prove2.me/submissions/59958e4a-a523-4452-8a91-4d8c001cb40a

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
theorem _root_.solution (hA : ANum) (hD : DLower) (hS : Sandwich) : CHLower := by
  intro x hx
  have h1 := hD x hx
  have h2 := (hS x (by linarith)).2
  have h3 := mul_le_mul_of_nonneg_right hA.1 (by linarith : (0 : ℝ) ≤ x)
  linarith
end PI.PC
