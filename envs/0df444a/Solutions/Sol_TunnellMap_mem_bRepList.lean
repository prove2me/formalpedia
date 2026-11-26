-- Prove2me | solution 1 for TunnellMap.mem_bRepList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:34:25.384088+00:00
-- url     : https://prove2.me/submissions/dd1b0230-0841-45f5-8c4d-f6853ed6f06c

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
import Theorems.Thm_TunnellMap_mem_sourceTriples


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (p : BRep n) : p ∈ bRepList n := by
  refine List.mem_filterMap.mpr ⟨p.1, mem_sourceTriples p.2, ?_⟩
  rw [dif_pos p.2]
  rfl
end TunnellMap
