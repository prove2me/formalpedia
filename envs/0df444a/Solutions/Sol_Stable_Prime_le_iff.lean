-- Prove2me | solution 1 for Stable.Prime.le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:49:24.237797+00:00
-- url     : https://prove2.me/submissions/d7117757-43e2-4746-a5cc-908593249675

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime
namespace Stable.Prime
theorem _root_.solution {p q : Prime F} : p ≤ q ↔ p.val ⊆ q.val := Iff.rfl
end Stable.Prime
