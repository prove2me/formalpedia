-- Prove2me | solution 1 for TunnellMap.reduceFrame_alpha_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:52.14037+00:00
-- url     : https://prove2.me/submissions/c0344706-c1b7-4e5f-952a-5edcf64b8173

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_isLagrangeGaussReduced_reduceFrame
import Theorems.Thm_TunnellMap_OrderedGenerator_reduced_alpha_square_bound


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (F : OrthogonalFrame p) :
    3 * alpha (reduceFrame F) ^ 2 ≤ 4 * dot p p :=
  reduced_alpha_square_bound _ (isLagrangeGaussReduced_reduceFrame F)
end TunnellMap
