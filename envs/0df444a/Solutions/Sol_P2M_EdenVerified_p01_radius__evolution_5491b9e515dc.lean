-- Prove2me | solution 1 for P2M_EdenVerified_p01_radius__evolution_5491b9e515dc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:10.864597+00:00
-- url     : https://prove2.me/submissions/5c51635c-73bf-4410-8e0d-43866f8c66ba

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_P2M_Eden_radius__evolution_5f79e8068ad6


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    Real.sqrt (radiusSq₁ (evolution c t p)) = radiusEvolution t (Real.sqrt (radiusSq₁ p)) :=
  @Eden.radius₁_evolution
end EdenVerified
