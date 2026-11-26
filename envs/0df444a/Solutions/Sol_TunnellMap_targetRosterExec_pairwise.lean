-- Prove2me | solution 1 for TunnellMap.targetRosterExec_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:33:43.011196+00:00
-- url     : https://prove2.me/submissions/fc323677-c05f-49d0-b1a5-507090d7f2d9

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} :
    (targetRosterExec n).Pairwise fun a b => aResidualLexKey a ≤ aResidualLexKey b := by
  refine List.Pairwise.imp ?_ (List.pairwise_insertionSort ALexLe _)
  intro a b hab
  exact (aLexLe_iff a b).mp hab
end TunnellMap
