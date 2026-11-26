-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.targetOfValid_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:15.48863+00:00
-- url     : https://prove2.me/submissions/018185e6-06e7-47a9-b8cf-f3ccc4b367e1

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
    directionKey (dValue F i.1) =
      representativeEdgeKey s (targetOfValid s F i) := by
  have hfilters : PassesFilters s F i.1 :=
    (mem_validIndices_iff s F i.1).mp i.2 |>.2
  exact (Classical.choose_spec hfilters.2.2.2.2).2
end TunnellMap.OrderedGenerator
