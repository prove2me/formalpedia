-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.orderedIndexList_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:45.381331+00:00
-- url     : https://prove2.me/submissions/b85d9f20-34ac-4360-acf9-0887f18f52f2

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
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (orderedIndexList s F).Nodup := by
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  exact Finset.sort_nodup ((validIndices s F).attach) (· ≤ ·)
end TunnellMap.OrderedGenerator
