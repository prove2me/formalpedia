-- Prove2me | solution 1 for TunnellMap.reduceFrame_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:35.573849+00:00
-- url     : https://prove2.me/submissions/90dda84a-3826-4fde-b61f-92ad7af9e79f

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
    (reduceFrame F).z = F.z := rfl
end TunnellMap
