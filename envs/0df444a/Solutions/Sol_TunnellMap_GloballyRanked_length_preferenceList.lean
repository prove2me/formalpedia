-- Prove2me | solution 1 for TunnellMap.GloballyRanked.length_preferenceList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:39.052592+00:00
-- url     : https://prove2.me/submissions/06b0e56f-31e5-4fe7-b64c-80107155ae60

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).length = Fintype.card T := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : ((Finset.univ : Finset T).sort (α := T) (· ≤ ·)).length = Fintype.card T := by
    simp
  exact h
end TunnellMap.GloballyRanked
