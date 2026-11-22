-- Prove2me | solution 1 for Stable.hist_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:39:02.79879+00:00
-- url     : https://prove2.me/submissions/56ad79db-d70a-4985-acde-c5d871ff12db

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
theorem _root_.solution (hc : F.Config c) (hx : x ∈ c) : hist F c x ⊆ c :=
  fun _ hy => Set.mem_sInter.mp hy c ⟨hc, subset_rfl, hx⟩
end Stable
