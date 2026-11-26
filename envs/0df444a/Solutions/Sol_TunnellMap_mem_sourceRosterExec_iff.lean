-- Prove2me | solution 1 for TunnellMap.mem_sourceRosterExec_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:05.550318+00:00
-- url     : https://prove2.me/submissions/cb047b95-df69-4149-9f1c-321a48032dbf

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_mem_sourceRosterUnsorted_iff

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔ IsSourceRosterTriple n x.1.1 := by
  rw [sourceRosterExec, (List.perm_insertionSort _ _).mem_iff, List.mem_dedup,
    mem_sourceRosterUnsorted_iff]
end TunnellMap
