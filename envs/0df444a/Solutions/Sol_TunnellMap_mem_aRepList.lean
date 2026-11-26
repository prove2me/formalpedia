-- Prove2me | solution 1 for TunnellMap.mem_aRepList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:45:28.621502+00:00
-- url     : https://prove2.me/submissions/c1c12a09-81f7-4551-9f33-dd357ad40470

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_mem_targetTriples


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : ARep n) : p ∈ aRepList n := by
  refine List.mem_filterMap.mpr ⟨p.1, mem_targetTriples p.2, ?_⟩
  rw [dif_pos p.2]
  rfl
end TunnellMap
