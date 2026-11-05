-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.capacity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:23:59.240558+00:00
-- url     : https://prove2.me/submissions/1efbbba4-53a3-458d-b8a8-bbc9ef3e8770

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution (D E U : ℕ) : 256≤capacity D E U := by
  have hp : 1≤(U+1)^E := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout
