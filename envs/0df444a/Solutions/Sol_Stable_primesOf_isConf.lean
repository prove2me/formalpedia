-- Prove2me | solution 1 for Stable.primesOf_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:07.822024+00:00
-- url     : https://prove2.me/submissions/bb2b94d4-22df-45b0-b42d-87d354a3cc22

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution {c : Set F.Event} (hc : F.Config c) :
    isConf (toPES F) (primesOf F c) :=
  ⟨fun h₁ h₂ hcf => hcf ⟨c, hc, h₁, h₂⟩, fun hp hle => Set.Subset.trans hle hp⟩
end Stable
