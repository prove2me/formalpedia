-- Prove2me | solution 1 for Stable.mem_flatten_primesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:08.919973+00:00
-- url     : https://prove2.me/submissions/e5b4f122-f6b2-419a-bc81-62127a502744

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_hist_mem
import Theorems.Thm_Stable_hist_subset


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {x : F.Event} (hx : x ∈ c) : x ∈ flatten F (primesOf F c) :=
  Set.mem_biUnion (show histPrime hF hc hx ∈ primesOf F c from hist_subset hc hx)
    (hist_mem (x := x))
end Stable
