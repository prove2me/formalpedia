-- Prove2me | solution 1 for Stable.subset_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:43:52.776895+00:00
-- url     : https://prove2.me/submissions/55a40565-1010-4291-80f2-bc50dae486cd

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution {S : Set (Prime F)} {p : Prime F} (hp : p ∈ S) :
    p.val ⊆ flatten F S :=
  fun _ hx => Set.mem_biUnion hp hx
end Stable
