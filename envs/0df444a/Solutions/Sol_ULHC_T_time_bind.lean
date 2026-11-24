-- Prove2me | solution 1 for ULHC.T.time_bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:36.715809+00:00
-- url     : https://prove2.me/submissions/c303be5f-e2d4-473e-a932-c348846b5d9b

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
end ULHC.T
