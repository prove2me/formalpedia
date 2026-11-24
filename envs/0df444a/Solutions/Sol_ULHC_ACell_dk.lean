-- Prove2me | solution 1 for ULHC.ACell.dk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:35.630797+00:00
-- url     : https://prove2.me/submissions/298dd48c-d957-4019-87ee-0dc0da877eca

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_ne

set_option autoImplicit true
open ULHC
open Finset Classical
open ULHC.ACell
variable (C : ACell)
namespace ULHC.ACell
theorem _root_.solution : C.d ≠ C.k := C.h2.ne
end ULHC.ACell
