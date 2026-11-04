-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaLayout.capacity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:32:32.472445+00:00
-- url     : https://prove2.me/submissions/e414b742-1e3d-444b-bfd9-5822f42d4b93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaLayout
namespace ThreeSum.WeightedGlobalArenaLayout
theorem _root_.solution (D E U : ℕ) : 256≤capacity D E U := by
  have hp : 1≤(U+1)^E := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  nlinarith
end ThreeSum.WeightedGlobalArenaLayout
