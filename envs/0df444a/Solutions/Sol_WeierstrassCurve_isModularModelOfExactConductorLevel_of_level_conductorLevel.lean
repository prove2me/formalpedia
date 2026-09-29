-- Prove2me | solution 1 for WeierstrassCurve.isModularModelOfExactConductorLevel_of_level_conductorLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/800bd7a8-9083-5417-88a4-51ea54832007

import Mathlib
import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_WeierstrassCurve_ModularityLiftingConductor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel

set_option autoImplicit false

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h : W.IsModularModelOfLevel W.conductorLevel) :
    W.IsModularModelOfExactConductorLevel :=
  ⟨W.conductorLevel, W.conductorLevel_pos, W.squarefree_conductorLevel,
    fun _ hq => W.prime_dvd_conductorLevel_iff hΔ hq, h⟩

end S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel
end P2MW
export P2MW.S_WeierstrassCurve_isModularModelOfExactConductorLevel_of_level_conductorLevel (solution)
