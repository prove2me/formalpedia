-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.orderedIndexList_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:05.72063+00:00
-- url     : https://prove2.me/submissions/60956caa-9189-40bf-9bbd-af31dd43380d

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
    (orderedIndexList s F).Pairwise fun i j =>
      directionKey (dValue F i.1) ≤ directionKey (dValue F j.1) := by
  letI : LinearOrder {i // i ∈ validIndices s F} :=
    LinearOrder.lift' (fun i => directionKey (dValue F i.1))
      (validIndex_key_injective s F)
  exact Finset.pairwise_sort ((validIndices s F).attach) (· ≤ ·)
end TunnellMap.OrderedGenerator
