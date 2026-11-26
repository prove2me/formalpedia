-- Prove2me | solution 1 for TunnellMap.sourceRosterExec_eq_sourceRoster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:46:29.051709+00:00
-- url     : https://prove2.me/submissions/6c9fb2f7-b8af-467f-9843-b405aa324f7a

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_sourceRosterExec_nodup
import Theorems.Thm_TunnellMap_sourceRosterExec_pairwise
import Theorems.Thm_TunnellMap_mem_sourceRosterExec_iff_canonical
import Theorems.Thm_TunnellMap_mem_sourceRoster_iff
import Theorems.Thm_TunnellMap_sourceRoster_nodup
import Theorems.Thm_TunnellMap_sourceRoster_pairwise

set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA
namespace TunnellMap
theorem _root_.solution :
    sourceRosterExec n = sourceRoster n := by
  refine List.Perm.eq_of_pairwise ?_ sourceRosterExec_pairwise sourceRoster_pairwise ?_
  · intro a b _ _ hab hba
    exact bResidualLexKey_injective (le_antisymm hab hba)
  · refine (List.perm_ext_iff_of_nodup sourceRosterExec_nodup sourceRoster_nodup).mpr ?_
    intro x
    rw [mem_sourceRosterExec_iff_canonical, mem_sourceRoster_iff]
end TunnellMap
