-- Prove2me | solution 1 for Stable.hist_config
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:39:17.260984+00:00
-- url     : https://prove2.me/submissions/73c65a7b-f51d-428b-9152-34accaa1c33a

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*}
open Stable
variable {F : ConfFamily L}
variable {c : Set F.Event} {x : F.Event}
namespace Stable
theorem _root_.solution (hF : Stable F) (hc : F.Config c) (hx : x ∈ c) :
    F.Config (hist F c x) :=
  hF ⟨c, hc, subset_rfl, hx⟩ (fun _ hm => hm.1) hc (fun _ hm => hm.2.1)
end Stable
