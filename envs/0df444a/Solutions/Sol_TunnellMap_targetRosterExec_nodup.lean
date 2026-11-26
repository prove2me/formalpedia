-- Prove2me | solution 1 for TunnellMap.targetRosterExec_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:40:25.569369+00:00
-- url     : https://prove2.me/submissions/04c8f388-e397-4f67-84b1-7c3781d24420

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} : (targetRosterExec n).Nodup :=
  ((List.perm_insertionSort (ALexLe (n := n)) _).nodup_iff).mpr (List.nodup_dedup _)
end TunnellMap
