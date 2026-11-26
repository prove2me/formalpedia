-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferenceList_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:02.536105+00:00
-- url     : https://prove2.me/submissions/95e600ef-f0ae-4344-ad78-d40260223eb2

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Nodup := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.sort_nodup (Finset.univ : Finset T) (· ≤ ·)
end TunnellMap.GloballyRanked
