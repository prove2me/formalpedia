-- Prove2me | solution 1 for P2M_EdenVerified_p01_radius__evolution_d91fbbccba93
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:11.698482+00:00
-- url     : https://prove2.me/submissions/1865d126-ba83-4611-aec1-b8160d2dca09

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_P2M_Eden_radius__evolution_affebfa495cb


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₂ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₂ p)) :=
  @Eden.radius₂_evolution
end EdenVerified
