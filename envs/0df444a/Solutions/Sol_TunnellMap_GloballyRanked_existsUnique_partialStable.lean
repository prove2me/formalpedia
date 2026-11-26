-- Prove2me | solution 1 for TunnellMap.GloballyRanked.existsUnique_partialStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:44:14.348435+00:00
-- url     : https://prove2.me/submissions/1b1377e4-b5e4-4ad1-abc4-4adc2a8cb287

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
import Theorems.Thm_TunnellMap_GloballyRanked_stable_to_partialStable
import Theorems.Thm_TunnellMap_GloballyRanked_partialStable_unique
import Theorems.Thm_TunnellMap_GloballyRanked_stable_exists


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃! M : PartialEquiv S T, I.PartialStable M := by
  classical
  obtain ⟨M, hM⟩ := stable_exists I hcard
  refine ⟨M.toPartialEquiv, stable_to_partialStable I M hM, ?_⟩
  intro N hN
  exact partialStable_unique I hcard N M.toPartialEquiv hN
    (stable_to_partialStable I M hM)
end TunnellMap.GloballyRanked
