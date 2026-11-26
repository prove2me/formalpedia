-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.validIndex_key_eq_orbitEdgeKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:55.410773+00:00
-- url     : https://prove2.me/submissions/9fb3fcce-11f4-4427-b895-a131fa893241

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_targetOfValid_key
import Theorems.Thm_TunnellMap_representativeEdgeKey_eq_orbitEdgeKey


set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    directionKey (dValue F i.1) =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        (targetOrbitOfValid hnpos s F i) := by
  calc
    directionKey (dValue F i.1) =
        representativeEdgeKey s (targetOfValid s F i) :=
      targetOfValid_key s F i
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((aResidualInvolution n hnpos).orbit (targetOfValid s F i)) :=
      representativeEdgeKey_eq_orbitEdgeKey hnpos s (targetOfValid s F i)
    _ = orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        (targetOrbitOfValid hnpos s F i) := rfl
end TunnellMap.OrderedGenerator
