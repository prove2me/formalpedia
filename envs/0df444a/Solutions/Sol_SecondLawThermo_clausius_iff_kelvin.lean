-- Prove2me | solution 1 for SecondLawThermo.clausius_iff_kelvin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:41:59.476637+00:00
-- url     : https://prove2.me/submissions/f19aca1e-e6d9-4cc4-be1e-7026d4953b61

import Definitions.Def_SecondLawThermo_Defs
import Mathlib
import Theorems.Thm_SecondLawThermo_clausius_of_kelvin
import Theorems.Thm_SecondLawThermo_kelvin_of_clausius

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ] [Nontrivial Θ] (𝒞 : Set (SecondLawThermo.Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCarnot : CarnotEnginesExist 𝒞) :
    ClausiusStatement 𝒞 ↔ KelvinStatement 𝒞 := by
  constructor
  · intro hC
    exact SecondLawThermo.kelvin_of_clausius 𝒞 h𝒞 hCarnot hC
  · intro hK
    exact SecondLawThermo.clausius_of_kelvin 𝒞 h𝒞 hCarnot hK
