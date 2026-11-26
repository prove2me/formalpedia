-- Prove2me | solution 1 for TunnellMap.lgReduce_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:58.38716+00:00
-- url     : https://prove2.me/submissions/7c5c8873-4424-48af-8b2e-7ffeff5893b3

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_lgReduceAux_reduced
import Theorems.Thm_TunnellMap_lgSelect_reduced

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution (u v : Triple) : IsReducedPair (lgReduce u v) :=
  lgSelect_reduced (lgReduceAux_reduced u v)
end TunnellMap
