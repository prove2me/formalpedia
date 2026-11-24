-- Prove2me | solution 1 for ULHC.creach_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:20.91305+00:00
-- url     : https://prove2.me/submissions/6d4aa587-d15d-4fb2-8f58-72326d6db667

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (x : Pt) (k : ℕ) :
    creach F x (k + 1) = creach F x k ∪ (creach F x k).biUnion (fnbr F) := rfl
end ULHC
