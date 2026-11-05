-- Prove2me | solution 1 for SelectedFloorTransfer.depth_below_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/4b512822-86d8-4e7f-9acb-517561f61f81

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorDepth_depth_base


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (e : ℕ) (he : e < m) : depth e = 0 :=
  FloorDepth.depth_base m maxChild maxChild_lt e he
end SelectedFloorTransfer
