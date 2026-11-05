-- Prove2me | solution 1 for SelectedFloorTransfer.child_row_stock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/0e40b272-0393-42d9-a319-4edf3aa2af0a

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_SelectedFloorTransfer_width_le_max
import Theorems.Thm_FloorDepth_child_row_stock


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (r : Row) (hr : r ∈ rows) (e R : ℕ) (he : m ≤ e)
    (stock : W ^ depth e ∣ R) : W ^ depth (r.width * (e / m)) ∣ R / W :=
  FloorDepth.child_row_stock m maxChild r.width e W R maxChild_lt (width_le_max r hr) he
    (by norm_num [W]) stock
end SelectedFloorTransfer
