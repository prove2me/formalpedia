-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.targetOrbitOfValid_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:15.7018+00:00
-- url     : https://prove2.me/submissions/04a9bf00-1995-4f08-be71-deaa8a9fc175

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_validIndex_key_eq_orbitEdgeKey

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    Function.Injective (targetOrbitOfValid hnpos s F) := by
  intro i j horbit
  apply validIndex_eq_of_directionKey_eq s F
  calc
    directionKey (dValue F i.1) =
        orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
          (targetOrbitOfValid hnpos s F i) :=
      validIndex_key_eq_orbitEdgeKey hnpos s F i
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
          (targetOrbitOfValid hnpos s F j) := by rw [horbit]
    _ = directionKey (dValue F j.1) :=
      (validIndex_key_eq_orbitEdgeKey hnpos s F j).symm
end TunnellMap.OrderedGenerator
