-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.incidentStream_exactly_once
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:28.669862+00:00
-- url     : https://prove2.me/submissions/e801a54a-18f9-49e0-be87-0a0620e38136

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_nodup
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_incidentStream

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃! i : Fin (incidentStream hnpos s F).length,
      (incidentStream hnpos s F).get i = tOrbit := by
  obtain ⟨i, hi⟩ := List.get_of_mem
    (mem_incidentStream hn hnpos s F tOrbit)
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (incidentStream_nodup hnpos s F).injective_get (hj.trans hi.symm)
end TunnellMap.OrderedGenerator
