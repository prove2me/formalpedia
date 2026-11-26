-- Prove2me | solution 1 for TunnellMap.lgReduce_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:58.805768+00:00
-- url     : https://prove2.me/submissions/ce925b11-8b34-4ce5-961d-82e94d13c2be

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution {u v u' v' : Triple} (hu : u = u') (hv : v = v') :
    lgReduce u v = lgReduce u' v' := by rw [hu, hv]
end TunnellMap
