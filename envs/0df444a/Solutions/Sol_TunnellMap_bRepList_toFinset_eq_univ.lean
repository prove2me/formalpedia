-- Prove2me | solution 1 for TunnellMap.bRepList_toFinset_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:41:21.765533+00:00
-- url     : https://prove2.me/submissions/c48fb51d-7b62-463f-8257-bce7be1d41ec

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_mem_bRepList

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) : (bRepList n).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun p => List.mem_toFinset.mpr (mem_bRepList p)
end TunnellMap
