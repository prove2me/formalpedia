-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_parameter_comparison
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:31.588307+00:00
-- url     : https://prove2.me/submissions/1338e640-340e-4148-9429-18581fcd09f8

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_cavity_transport
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_bethe_strict_transport
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_bethe_dirac_zero
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 3 ≤ d) (α α' : ℝ)
    (hα : 0 < α) (hlt : α < α') (hα' : α' < 1 / 2)
    (hrs : VariationalRS .hardcore d α') :
    Condition1 .hardcore d α ∧ VariationalRS .hardcore d α := by
  have ha1 : α < 1/2 := by linarith
  have hstrict : ∀ ν ∈ cavityLaws .hardcore α, ν ≠ diracPi .hardcore α → betheK .hardcore α d ν < 0 := by
    intro ν hν hne
    obtain ⟨hc0,hc1,ν',hν',hn',hmap⟩ := hardcore_cavity_transport α α' hα hlt hα' ν hν
    have hcmp := hardcore_bethe_strict_transport d (by omega) α α' hα hlt hα' ν hν hne ν' hν' hmap
    exact lt_of_lt_of_le hcmp (hrs ν' hν')
  constructor
  · exact hstrict
  · intro ν hν
    by_cases heq : ν = diracPi .hardcore α
    · rw [heq,hardcore_bethe_dirac_zero d α hα ha1]
    · exact (hstrict ν hν heq).le
