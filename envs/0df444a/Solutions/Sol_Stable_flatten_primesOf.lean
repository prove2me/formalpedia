-- Prove2me | solution 1 for Stable.flatten_primesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:15.14233+00:00
-- url     : https://prove2.me/submissions/239c0680-d8d4-4f57-a86b-77739b316c60

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_mem_flatten_primesOf

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) {c : Set F.Event} (hc : F.Config c) :
    flatten F (primesOf F c) = c := by
  refine Set.Subset.antisymm ?_ fun x hx => mem_flatten_primesOf hF hc hx
  rintro x ⟨-, ⟨p, rfl⟩, -, ⟨hp, rfl⟩, hxp⟩
  exact hp hxp
end Stable
