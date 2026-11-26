-- Prove2me | solution 1 for TunnellMap.isLagrangeGaussReduced_reduceFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:52.091191+00:00
-- url     : https://prove2.me/submissions/e10a5681-ffde-42e2-9278-74410c22ddca

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_lgReduce_reduced

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (F : OrthogonalFrame p) :
    IsLagrangeGaussReduced (reduceFrame F) :=
  lgReduce_reduced F.e₁ F.e₂
end TunnellMap
