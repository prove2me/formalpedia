-- Prove2me | solution 1 for V3Glue.ChartInput.isReduced_Y
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/779a9fe6-1b25-51df-a90b-7eca1fcaf3d2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Glue_ChartInput_isReduced_Y

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N) (n : N)
    [IsReduced (C.Res n)] [IsLocallyNoetherian (C.Res n)] : IsReduced (C.Y n) := by
  haveI : Etale (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance
  exact Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (C.g n)

end S_V3Glue_ChartInput_isReduced_Y
end P2MW
export P2MW.S_V3Glue_ChartInput_isReduced_Y (solution)
