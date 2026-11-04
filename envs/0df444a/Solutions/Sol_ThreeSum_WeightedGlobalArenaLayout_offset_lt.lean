-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaLayout.offset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:43:07.910745+00:00
-- url     : https://prove2.me/submissions/0eea1525-005f-4c49-9060-341fd0024354

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_before

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaLayout
namespace ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C slot len offset : ℕ} (hoff : offset<len) (hlen : len≤C) :
    addr free C slot+offset<addr free C (slot+1) := by
  have hh := before (free := free) (show slot<slot+1 by omega) hlen
  omega
end ThreeSum.WeightedGlobalArenaLayout
