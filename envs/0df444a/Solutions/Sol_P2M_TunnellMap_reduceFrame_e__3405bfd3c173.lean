-- Prove2me | solution 1 for P2M_TunnellMap_reduceFrame_e__3405bfd3c173
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:09.202051+00:00
-- url     : https://prove2.me/submissions/1876242c-f3ee-4983-add1-88c29b754f19

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
    (reduceFrame F).e₂ = (lgReduce F.e₁ F.e₂).2 := rfl
end TunnellMap
