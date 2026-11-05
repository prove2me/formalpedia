-- Prove2me | solution 1 for SelectedFloorTransfer.depth_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/5cb563cc-73a7-46fc-84a3-63447b0b3d02

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorDepth_depth_step


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (e : ℕ) (he : m ≤ e) :
    depth e = 1 + depth (maxChild * (e / m)) :=
  FloorDepth.depth_step m maxChild maxChild_lt e he
end SelectedFloorTransfer
