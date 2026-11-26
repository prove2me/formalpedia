-- Prove2me | solution 1 for TunnellMap.GloballyRanked.exists_unique_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:18.022415+00:00
-- url     : https://prove2.me/submissions/eed3c4fb-8185-4b10-b68b-673cb6c284b4

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_stable_exists
import Theorems.Thm_TunnellMap_GloballyRanked_stable_unique


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃! M : S ≃ T, I.Stable M := by
  obtain ⟨M, hM⟩ := stable_exists I hcard
  refine ⟨M, hM, ?_⟩
  intro N hN
  exact stable_unique I N M hN hM
end TunnellMap.GloballyRanked
