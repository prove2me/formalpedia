-- Prove2me | solution 1 for P2M_Eden_radiusSq__evolution_lt_one_iff_5cac5d742e9b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:44.660324+00:00
-- url     : https://prove2.me/submissions/96abb5bb-eb3b-4258-b181-ec867d21a664

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_squaredRadiusEvolution_lt_one_iff
import Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    radiusSq₁ (evolution c t p) < 1 ↔ radiusSq₁ p < 1 := by
  rw [radiusSq₁_evolution c ht, squaredRadiusEvolution_lt_one_iff ht]
end Eden
