-- Prove2me | solution 1 for ULHC.ACell.ab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:34.452578+00:00
-- url     : https://prove2.me/submissions/06c69031-91ea-48ed-b62f-8b2fb085e0a9

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_ne

set_option autoImplicit true
open ULHC
open Finset Classical
open ULHC.ACell
variable (C : ACell)
namespace ULHC.ACell
theorem _root_.solution : C.a ≠ C.b := C.h1.ne
end ULHC.ACell
