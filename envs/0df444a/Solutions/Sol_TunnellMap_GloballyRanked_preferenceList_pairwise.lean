-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferenceList_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:48.208968+00:00
-- url     : https://prove2.me/submissions/67dc9416-f08c-4d66-be24-d7d2a688ef69

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Pairwise fun t₁ t₂ => I.rank s t₁ ≤ I.rank s t₂ := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.pairwise_sort (Finset.univ : Finset T) (· ≤ ·)
end TunnellMap.GloballyRanked
