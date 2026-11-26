-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.incidentStream_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:20.581821+00:00
-- url     : https://prove2.me/submissions/f26b7b24-76ef-40c5-abfb-69bf7d8fdbbe

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_targetOrbitOfValid_injective
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_nodup

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Nodup := by
  exact (orderedIndexList_nodup s F).map
    (targetOrbitOfValid_injective hnpos s F)
end TunnellMap.OrderedGenerator
