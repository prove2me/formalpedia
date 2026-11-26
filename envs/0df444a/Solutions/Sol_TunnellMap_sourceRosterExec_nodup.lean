-- Prove2me | solution 1 for TunnellMap.sourceRosterExec_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:16.276833+00:00
-- url     : https://prove2.me/submissions/cdd14587-307a-4425-9c9d-568c9ebecdf2

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} : (sourceRosterExec n).Nodup :=
  ((List.perm_insertionSort (BLexLe (n := n)) _).nodup_iff).mpr (List.nodup_dedup _)
end TunnellMap
