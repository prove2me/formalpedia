-- Prove2me | solution 1 for TunnellMap.BlockGen.fullTrace_key_eq_incidentStream
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:48:35.493499+00:00
-- url     : https://prove2.me/submissions/076b351e-c6d0-4c8c-8684-0f10964086f9

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Theorems.Thm_TunnellMap_OrderedGenerator_validIndex_key_eq_orbitEdgeKey


set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).map IncidentRecord.key =
      (incidentStream hnpos s F).map
        (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) := by
  rw [fullTrace_eq_map_orderedIndexList, incidentStream, List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro i _
  exact (recordOf_key_of_valid F i.2).trans (validIndex_key_eq_orbitEdgeKey hnpos s F i)
end TunnellMap.BlockGen
