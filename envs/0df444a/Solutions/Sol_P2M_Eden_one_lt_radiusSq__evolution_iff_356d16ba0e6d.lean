-- Prove2me | solution 1 for P2M_Eden_one_lt_radiusSq__evolution_iff_356d16ba0e6d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:19.368157+00:00
-- url     : https://prove2.me/submissions/72807b7a-5beb-407f-8794-c6c7ee473823

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_one_lt_squaredRadiusEvolution_iff
import Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    1 < radiusSq₁ (evolution c t p) ↔ 1 < radiusSq₁ p := by
  rw [radiusSq₁_evolution c ht, one_lt_squaredRadiusEvolution_iff ht]
end Eden
