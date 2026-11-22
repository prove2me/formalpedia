-- Prove2me | solution 1 for PES.stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:49:04.387799+00:00
-- url     : https://prove2.me/submissions/81ccffd7-a3f7-4fe7-a12f-f71e175b072c

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*}
namespace PES
theorem _root_.solution (P : PES L) : Stable P.toFamily := by
  intro S z hne hS _ _
  obtain ⟨m, hm⟩ := hne
  exact ⟨fun h₁ h₂ => (hS m hm).1 (Set.mem_sInter.mp h₁ m hm) (Set.mem_sInter.mp h₂ m hm),
         fun he hle => Set.mem_sInter.mpr
           (fun n hn => (hS n hn).2 (Set.mem_sInter.mp he n hn) hle)⟩
end PES
