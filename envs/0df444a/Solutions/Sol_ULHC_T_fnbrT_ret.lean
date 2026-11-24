-- Prove2me | solution 1 for ULHC.T.fnbrT_ret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:11.561797+00:00
-- url     : https://prove2.me/submissions/95be5006-2f27-4c39-a2eb-ad0d25868b03

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (F : Finset Edge) (u : Pt) : (fnbrT F u).ret = fnbr F u := rfl
end ULHC.T
