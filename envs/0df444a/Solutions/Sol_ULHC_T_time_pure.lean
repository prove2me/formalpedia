-- Prove2me | solution 1 for ULHC.T.time_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:07:10.342772+00:00
-- url     : https://prove2.me/submissions/956b6c39-d137-4502-891a-933438a3c228

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (a : α) : (pure a : TimeM α).time = 0 := rfl
end ULHC.T
