-- Prove2me | solution 1 for TunnellMap.GloballyRanked.partialStable_to_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:19:13.449282+00:00
-- url     : https://prove2.me/submissions/4908cd07-a758-4e02-8ddd-a62bcd608cd0

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LT K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M : PartialEquiv S T) (hM : I.PartialStable M) :
    I.Stable (partialEquivToEquiv M
      (partialStable_isPerfect I hcard M hM).1
      (partialStable_isPerfect I hcard M hM).2) := by
  intro s t hblock
  apply hM s t
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  · simpa [partialEquivToEquiv] using hblock.1
  · simpa [partialEquivToEquiv] using hblock.2
end TunnellMap.GloballyRanked
