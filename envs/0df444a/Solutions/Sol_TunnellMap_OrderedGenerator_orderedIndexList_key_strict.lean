-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.orderedIndexList_key_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:21.12652+00:00
-- url     : https://prove2.me/submissions/23478bdf-c503-4e67-9a80-97ffeb2e1e90

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_pairwise
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_nodup

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (orderedIndexList s F).length} (hij : i < j) :
    directionKey (dValue F ((orderedIndexList s F).get i).1) <
      directionKey (dValue F ((orderedIndexList s F).get j).1) := by
  have hle := (orderedIndexList_pairwise s F).rel_get_of_lt hij
  have hne : (orderedIndexList s F).get i ≠ (orderedIndexList s F).get j := by
    intro h
    exact (ne_of_lt hij) ((orderedIndexList_nodup s F).injective_get h)
  apply lt_of_le_of_ne hle
  intro hkey
  exact hne (validIndex_key_injective s F hkey)
end TunnellMap.OrderedGenerator
