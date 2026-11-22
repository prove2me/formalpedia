-- Prove2me | solution 1 for Stable.Prime.eq_hist_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:43:49.383681+00:00
-- url     : https://prove2.me/submissions/4fa1ab16-11a1-4404-ba98-e87ab1071b30

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime
namespace Stable.Prime
theorem _root_.solution (p : Prime F) : p.val = hist F p.val (top p) :=
  (Classical.choose_spec p.2.2).2
end Stable.Prime
