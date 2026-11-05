-- Prove2me | solution 1 for SelectedFloorTransfer.child_depth_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/2de37625-7f2e-4525-acb2-2d800eba1ddf

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_SelectedFloorTransfer_width_le_max
import Theorems.Thm_FloorDepth_child_depth_drop


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (r : Row) (hr : r ∈ rows) (e : ℕ) (he : m ≤ e) :
    depth (r.width * (e / m)) + 1 ≤ depth e :=
  FloorDepth.child_depth_drop m maxChild r.width e maxChild_lt (width_le_max r hr) he
end SelectedFloorTransfer
