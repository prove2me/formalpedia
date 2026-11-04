-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaLayout.region_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:43:05.217019+00:00
-- url     : https://prove2.me/submissions/1602e508-4dcb-4dda-9c04-d604668c407c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaLayout
namespace ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C slot len space : ℕ} (hslot : slot<slots)
    (hlen : len≤C) (hend : finish free C≤space) : addr free C slot+len≤space :=
  (before hslot hlen).trans hend
end ThreeSum.WeightedGlobalArenaLayout
