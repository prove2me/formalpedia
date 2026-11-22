-- Prove2me | solution 1 for PES.coherent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:10:47.416129+00:00
-- url     : https://prove2.me/submissions/8ede4296-b12c-407f-ae59-1981d69a0c5e

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*}

theorem PES.coherent (P : PES L) : Coherent P.toFamily := by
  intro S z hS hz hSz
  change isConf P z at hz
  change isConf P (⋃₀ S)
  refine ⟨fun {e₁ e₂} h1 h2 => hz.1 ?_ ?_, fun {e e'} he hle => ?_⟩
  · obtain ⟨x, hx, h⟩ := h1; exact hSz x hx h
  · obtain ⟨x, hx, h⟩ := h2; exact hSz x hx h
  · obtain ⟨x, hx, h⟩ := he
    have hxc : isConf P x := hS x hx
    exact ⟨x, hx, hxc.2 h hle⟩

theorem solution (P : PES L) : Coherent P.toFamily := PES.coherent P
