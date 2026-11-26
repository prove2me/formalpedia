-- Prove2me | solution 1 for TunnellMap.mem_targetRosterExec_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:46:49.954194+00:00
-- url     : https://prove2.me/submissions/810707f5-8b5e-445b-b8b9-0ed8cd1b4f12

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_mem_targetRosterUnsorted_iff

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (x : AResidual n) :
    x ∈ targetRosterExec n ↔ IsTargetRosterTriple n x.1.1 := by
  rw [targetRosterExec, (List.perm_insertionSort _ _).mem_iff, List.mem_dedup,
    mem_targetRosterUnsorted_iff]
end TunnellMap
