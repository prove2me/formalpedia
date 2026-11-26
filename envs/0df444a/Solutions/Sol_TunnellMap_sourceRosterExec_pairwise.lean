-- Prove2me | solution 1 for TunnellMap.sourceRosterExec_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:22.654821+00:00
-- url     : https://prove2.me/submissions/5ec10940-7c37-48ed-933d-6d915d86ec92

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} :
    (sourceRosterExec n).Pairwise fun a b => bResidualLexKey a ≤ bResidualLexKey b := by
  refine List.Pairwise.imp ?_ (List.pairwise_insertionSort BLexLe _)
  intro a b hab
  exact (bLexLe_iff a b).mp hab
end TunnellMap
