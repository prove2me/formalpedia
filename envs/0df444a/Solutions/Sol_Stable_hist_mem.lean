-- Prove2me | solution 1 for Stable.hist_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:38:56.736801+00:00
-- url     : https://prove2.me/submissions/9c2fae12-0b2d-4516-96f2-b8290f869eb8

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
theorem _root_.solution : x ∈ hist F c x :=
  Set.mem_sInter.mpr (fun _ hm => hm.2.2)
end Stable
