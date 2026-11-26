-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.targetOfValid_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:41.999065+00:00
-- url     : https://prove2.me/submissions/dc669d75-e360-4501-a35e-c3101997767b

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    residualTargetLift (targetOfValid s F i) = targetValue s F i.1 := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact (Classical.choose_spec hfilters.2.2.2.2).1
end TunnellMap.OrderedGenerator
