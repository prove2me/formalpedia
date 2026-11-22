-- Prove2me | solution 1 for Stable.hist_least
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:38:59.742017+00:00
-- url     : https://prove2.me/submissions/ef6f78f4-8bd4-4aac-86be-2d1c5ff922af

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
theorem _root_.solution {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hxm : x ∈ m) :
    hist F c x ⊆ m :=
  fun _ hy => Set.mem_sInter.mp hy m ⟨hm, hmc, hxm⟩
end Stable
