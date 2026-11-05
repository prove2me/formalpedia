-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.region_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:27:57.829634+00:00
-- url     : https://prove2.me/submissions/ed383752-830b-4ea8-bbbd-402ed23e967f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution {free C slot len space : ℕ} (hslot : slot<slots)
    (hlen : len≤C) (hend : finish free C≤space) : addr free C slot+len≤space :=
  (before hslot hlen).trans hend
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
