-- Prove2me | solution 1 for ULHC.T.ret_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:42.931663+00:00
-- url     : https://prove2.me/submissions/35f301cf-1084-4580-bef6-be79e90da65a

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (a : α) : (pure a : TimeM α).ret = a := rfl
end ULHC.T
