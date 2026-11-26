-- Prove2me | solution 1 for TDLC.Syntax.Example.routesDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:11.865034+00:00
-- url     : https://prove2.me/submissions/f4d308c3-3e4c-4ab0-a7c6-cd01b82fe1fe

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax

set_option autoImplicit true
open TDLC TDLC.Syntax
open TDLC.Syntax.Example
namespace TDLC.Syntax.Example
theorem _root_.solution : betaRoute ≠ etaRoute := by
  intro h
  have hp := congrArg Conv.parity h
  exact Bool.noConfusion hp
end TDLC.Syntax.Example
