-- Prove2me | solution 1 for SelectedFloorTransfer.exact_row_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/c7734733-5f4b-4959-bda7-7020641ccc6e

import Definitions.Def_FloorRecurrence
import Definitions.Def_SelectedProfileReal
import Definitions.Def_SelectedFloorTransfer
import Theorems.Thm_FloorDepth_row_split_exact


set_option autoImplicit true
open SelectedFloorTransfer
open SelectedProfileCertificate
namespace SelectedFloorTransfer
theorem _root_.solution (e R : ℕ) (he : m ≤ e) (stock : W ^ depth e ∣ R) :
    W * (R / W) = R := FloorDepth.row_split_exact m maxChild e W R maxChild_lt he stock
end SelectedFloorTransfer
