-- Prove2me | solution 1 for TunnellMap.reduceFrame_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:24:55.176142+00:00
-- url     : https://prove2.me/submissions/bdae4993-0b2a-48c6-ba28-1970b5380340

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}
namespace TunnellMap
theorem _root_.solution (F : OrthogonalFrame p) :
    dot (reduceFrame F).e₁ (reduceFrame F).e₁ * dot (reduceFrame F).e₂ (reduceFrame F).e₂ -
        dot (reduceFrame F).e₁ (reduceFrame F).e₂ ^ 2 = dot p p :=
  (reduceFrame F).gram_det
end TunnellMap
