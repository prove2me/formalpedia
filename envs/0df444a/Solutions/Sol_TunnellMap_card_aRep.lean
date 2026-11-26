-- Prove2me | solution 1 for TunnellMap.card_aRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:52:19.418827+00:00
-- url     : https://prove2.me/submissions/876e5b01-f328-4a08-aae6-34a385e5e452

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_aRepList_toFinset_eq_univ

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) : Fintype.card (ARep n) = (aRepList n).dedup.length := by
  rw [← Finset.card_univ, ← aRepList_toFinset_eq_univ, List.card_toFinset]
end TunnellMap
