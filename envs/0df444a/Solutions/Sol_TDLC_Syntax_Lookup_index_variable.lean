-- Prove2me | solution 1 for TDLC.Syntax.Lookup.index_variable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:01.224214+00:00
-- url     : https://prove2.me/submissions/8a2cf36e-fbf3-490d-9fa4-c5b2f3bfb065

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax

set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
namespace Lookup
theorem _root_.solution (h : Lookup Γ n a) : h.variable.index = n := by
  induction h with
  | zero => rfl
  | succ h ih => exact congrArg Nat.succ ih
end Lookup
end TDLC.Syntax
