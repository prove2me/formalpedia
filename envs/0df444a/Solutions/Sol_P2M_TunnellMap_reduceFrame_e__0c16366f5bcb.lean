-- Prove2me | solution 1 for P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:51.360839+00:00
-- url     : https://prove2.me/submissions/bd4bb740-e73a-462c-9075-82b5ff205323

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (F : OrthogonalFrame p) :
    (reduceFrame F).e₁ = (lgReduce F.e₁ F.e₂).1 := rfl
end TunnellMap
