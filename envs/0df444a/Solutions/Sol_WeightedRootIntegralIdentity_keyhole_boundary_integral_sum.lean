-- Prove2me | solution 1 for WeightedRootIntegralIdentity.keyhole_boundary_integral_sum
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T13:06:06.075678+00:00
-- url     : https://prove2.me/submissions/bbb3fc4b-1446-43bd-b396-985a2e589e69

import Mathlib
import Definitions.Def_keyholeLineIntegral

theorem solution
    (F : ℂ → ℂ) (a₀ a₁ r R : ℝ)
    (hdecomp : keyholeBoundaryIntegral F a₀ a₁ r R =
      keyholeUpperBankIntegral F a₀ a₁ + keyholeLowerBankIntegral F a₀ a₁ +
      keyholeInnerArcIntegral F r + keyholeOuterArcIntegral F R)
    (hbank : keyholeLowerBankIntegral F a₀ a₁ = - keyholeUpperBankIntegral F a₀ a₁)
    (hinner : keyholeInnerArcIntegral F r = 0)
    (houter : keyholeOuterArcIntegral F R = 0) :
    keyholeBoundaryIntegral F a₀ a₁ r R = 0 := by
  rw [hdecomp, hbank, hinner, houter]
  ring
