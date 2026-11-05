-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.offset_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:27:58.584779+00:00
-- url     : https://prove2.me/submissions/eb5e2a26-a6d6-4a89-b4f6-b94f3368884a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C slot len offset : ℕ} (hoff : offset<len) (hlen : len≤C) :
    addr free C slot+offset<addr free C (slot+1) := by
  have hh := before (free := free) (show slot<slot+1 by omega) hlen
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
