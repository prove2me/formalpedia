-- Prove2me | solution 1 for SelectedFloorTransfer.width_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/648f7da8-a131-4f96-aef1-eed8e18566ea

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_SelectedFloorTransfer_all_widths_le_max

set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (r : Row) (hr : r ∈ rows) : r.width ≤ maxChild := by
  exact of_decide_eq_true (List.all_eq_true.mp all_widths_le_max r hr)
end SelectedFloorTransfer
