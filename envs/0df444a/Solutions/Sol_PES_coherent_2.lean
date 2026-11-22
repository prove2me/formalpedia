-- Prove2me | solution 2 for PES.coherent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:57.278131+00:00
-- url     : https://prove2.me/submissions/0dd4ee9b-31b2-4222-8636-d364edfb9b80

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_General_Stable
import Mathlib.Data.Set.Lattice
import Definitions.Def_EventStructures_Stable_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*}
namespace PES
theorem _root_.solution (P : PES L) : Coherent P.toFamily := by
  intro S z hS hz hsub
  refine ⟨fun h₁ h₂ => ?_, fun he hle => ?_⟩
  · obtain ⟨m₁, hm₁, hx₁⟩ := h₁
    obtain ⟨m₂, hm₂, hx₂⟩ := h₂
    exact hz.1 (hsub m₁ hm₁ hx₁) (hsub m₂ hm₂ hx₂)
  · obtain ⟨m, hm, hx⟩ := he
    exact ⟨m, hm, (hS m hm).2 hx hle⟩
end PES
