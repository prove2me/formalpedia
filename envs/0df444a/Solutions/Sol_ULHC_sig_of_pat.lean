-- Prove2me | solution 1 for ULHC.sig_of_pat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:07.630382+00:00
-- url     : https://prove2.me/submissions/7549db65-c1b3-49a1-9198-81f76d6a38e8

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_strip_sig

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {z : Pt} {tf : Side} {m : ℕ} (hp : StripPat F z tf m) :
    SigFrom F z tf m 0 := fun _ _ hi => strip_sig hp hi
end ULHC
