-- Prove2me | solution 1 for SelectedFloorTransfer.depth_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/81405b3b-98f0-4266-af37-c886f81f2134

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorDepth_depth_mono


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution : Monotone depth := FloorDepth.depth_mono m maxChild maxChild_lt
end SelectedFloorTransfer
