-- Prove2me | solution 1 for P2M_EdenVerified_p16_radiusSq__evolution_81c316456352
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:26:04.104036+00:00
-- url     : https://prove2.me/submissions/edb49ddd-2f80-49ea-9e19-803db76e5df2

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_P2M_Eden_radiusSq__evolution_ce05ee2f5645


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace),
    radiusSq₂ (evolution c t p) = squaredRadiusEvolution t (radiusSq₂ p) :=
  @Eden.radiusSq₂_evolution
end EdenVerified
