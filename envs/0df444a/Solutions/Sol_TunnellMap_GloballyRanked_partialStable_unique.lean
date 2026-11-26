-- Prove2me | solution 1 for TunnellMap.GloballyRanked.partialStable_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:20:24.088958+00:00
-- url     : https://prove2.me/submissions/f582881a-9957-4228-beb2-c790d531fe79

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
import Theorems.Thm_TunnellMap_GloballyRanked_partialStable_to_stable
import Theorems.Thm_TunnellMap_GloballyRanked_stable_unique


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M N : PartialEquiv S T) (hM : I.PartialStable M)
    (hN : I.PartialStable N) : M = N := by
  classical
  let hMp := partialStable_isPerfect I hcard M hM
  let hNp := partialStable_isPerfect I hcard N hN
  let ME := partialEquivToEquiv M hMp.1 hMp.2
  let NE := partialEquivToEquiv N hNp.1 hNp.2
  have hME : I.Stable ME := partialStable_to_stable I hcard M hM
  have hNE : I.Stable NE := partialStable_to_stable I hcard N hN
  have heq : ME = NE := stable_unique I ME NE hME hNE
  apply PartialEquiv.ext
  · intro s
    exact congrArg (fun E : S ≃ T => E s) heq
  · intro t
    exact congrArg (fun E : S ≃ T => E.symm t) heq
  · exact hMp.1.trans hNp.1.symm
end TunnellMap.GloballyRanked
