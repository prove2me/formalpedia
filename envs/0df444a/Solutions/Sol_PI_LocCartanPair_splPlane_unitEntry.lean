-- Prove2me | solution 1 for PI.LocCartanPair.splPlane_unitEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:28.375798+00:00
-- url     : https://prove2.me/submissions/5909ae93-ce5c-4033-95e2-f76f3d44d9fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution [IsLocalRing R] {ι : Type} [Fintype ι] (w z : ι → R)
    (h : w ⬝ᵥ z = 1) : ∃ i, IsUnit (z i) := by
  by_contra hn
  push Not at hn
  have hm : w ⬝ᵥ z ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hn i))
  rw [h] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one
end PI.LocCartanPair
