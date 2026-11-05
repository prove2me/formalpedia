-- Prove2me | solution 1 for SelectedFloorTransfer.depth_logarithmic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/a158e404-6941-4438-9665-f1081dc01361

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorRecurrence_depth_log_bound


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (e : ℕ) (he : 0 < e) :
    (depth e : ℝ) ≤ 1 + Real.log (e : ℝ) / Real.log ((575 : ℝ) / 529) := by
  exact FloorRecurrence.depth_log_bound m maxChild maxChild_lt (by norm_num [maxChild]) e he
end SelectedFloorTransfer
