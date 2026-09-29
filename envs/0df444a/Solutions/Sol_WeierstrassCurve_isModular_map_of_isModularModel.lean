-- Prove2me | solution 1 for WeierstrassCurve.isModular_map_of_isModularModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/49d6e1ac-304b-5121-8a59-09742e0d749b

import Mathlib
import Definitions.Def_WeierstrassCurve_ModularityProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isModular_map_of_isModularModel

theorem solution {W : WeierstrassCurve ℤ} (h : W.IsModularModel) :
    (W.map (Int.castRingHom ℚ)).IsModular :=
  ⟨W, ⟨1, one_smul _ _⟩, h⟩

end S_WeierstrassCurve_isModular_map_of_isModularModel
end P2MW
export P2MW.S_WeierstrassCurve_isModular_map_of_isModularModel (solution)
