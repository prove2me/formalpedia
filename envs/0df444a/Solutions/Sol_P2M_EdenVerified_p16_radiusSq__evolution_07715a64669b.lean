-- Prove2me | solution 1 for P2M_EdenVerified_p16_radiusSq__evolution_07715a64669b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:51.888461+00:00
-- url     : https://prove2.me/submissions/667e3c0b-38ce-4374-bf34-c6a3375b8419

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_P2M_Eden_radiusSq__evolution_4de951b85a7e


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₁ (evolution c t p) = squaredRadiusEvolution t (radiusSq₁ p) :=
  @Eden.radiusSq₁_evolution
end EdenVerified
