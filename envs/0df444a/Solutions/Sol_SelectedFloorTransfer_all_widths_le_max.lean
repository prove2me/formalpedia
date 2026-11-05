-- Prove2me | solution 1 for SelectedFloorTransfer.all_widths_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/b690f83f-23b4-4034-a2e9-ee98d7b80ffb

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer

set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution : rows.all (fun r => decide (r.width ≤ maxChild)) = true := by
  decide +kernel
end SelectedFloorTransfer
