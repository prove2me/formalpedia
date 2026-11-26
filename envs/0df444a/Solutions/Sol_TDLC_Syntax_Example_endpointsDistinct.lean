-- Prove2me | solution 1 for TDLC.Syntax.Example.endpointsDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:11.33252+00:00
-- url     : https://prove2.me/submissions/d7fb0afe-89cb-4d0b-80d0-69e7b92ef49d

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax

set_option autoImplicit true
open TDLC TDLC.Syntax
open TDLC.Syntax.Example
namespace TDLC.Syntax.Example
theorem _root_.solution : source ≠ target := by
  intro h
  cases h
end TDLC.Syntax.Example
