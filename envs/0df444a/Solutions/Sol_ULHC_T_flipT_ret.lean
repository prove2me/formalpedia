-- Prove2me | solution 1 for ULHC.T.flipT_ret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:19.418526+00:00
-- url     : https://prove2.me/submissions/bbf16327-3c46-4d32-96bd-30dd796392ec

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
import Theorems.Thm_ULHC_APair_flip


set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (G : Finset Edge) (u : Pt) : (flipT G u).ret = flip G u := rfl
end ULHC.T
