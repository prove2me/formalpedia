-- Prove2me | solution 1 for ULHC.T.ret_bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:51.350679+00:00
-- url     : https://prove2.me/submissions/c74ad990-d145-402e-bb46-c0aaed7194ae

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (m : TimeM α) (f : α → TimeM β) : (m >>= f).ret = (f m.ret).ret := rfl
end ULHC.T
