-- Prove2me | solution 1 for Stable.Prime.top_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:43:38.890319+00:00
-- url     : https://prove2.me/submissions/c291d6f2-bad9-4034-a283-a2aba9b83c46

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime
namespace Stable.Prime
theorem _root_.solution (p : Prime F) : top p ∈ p.val := (Classical.choose_spec p.2.2).1
end Stable.Prime
