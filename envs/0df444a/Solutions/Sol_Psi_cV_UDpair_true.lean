-- Prove2me | solution 1 for Psi.cV_UDpair_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:18.376491+00:00
-- url     : https://prove2.me/submissions/c3078f89-78ab-4f55-bcfd-4b7ee10c5750

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution : countValleys [true, false] true = 1 := rfl
end Psi
