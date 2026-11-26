-- Prove2me | solution 1 for TunnellMap.card_bRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:43:53.562161+00:00
-- url     : https://prove2.me/submissions/f867553a-f54e-4a9d-9ef0-9c0bbf8c35ed

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_bRepList_toFinset_eq_univ

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) : Fintype.card (BRep n) = (bRepList n).dedup.length := by
  rw [← Finset.card_univ, ← bRepList_toFinset_eq_univ, List.card_toFinset]
end TunnellMap
