-- Prove2me | solution 1 for TunnellMap.aRepList_toFinset_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:48:25.996025+00:00
-- url     : https://prove2.me/submissions/d022e3d9-d4eb-4c7e-b82f-053f892660a7

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_mem_aRepList

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) : (aRepList n).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun p => List.mem_toFinset.mpr (mem_aRepList p)
end TunnellMap
