-- Prove2me | solution 1 for OpenGA.SurgeryContinuationData.allTime_or_breakdown
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T18:54:56.013908+00:00
-- url     : https://prove2.me/submissions/93bd703d-803d-4575-8849-8690c8461cc4

import Definitions.Def_OpenGA_SurgeryContinuationData
import Mathlib.Tactic

set_option autoImplicit false

open Set

theorem solution (C : OpenGA.SurgeryContinuationData) :
    (∀ T : ℝ, 0 ≤ T → C.DefinedUpTo T) ∨
      ∃ Tstar : ℝ, 0 < Tstar ∧ (∀ S : ℝ, 0 ≤ S → S < Tstar → C.DefinedUpTo S) ∧
        ¬ C.DefinedUpTo Tstar ∧ ¬ (C.surgeryTimes ∩ Iic Tstar).Finite := by
  by_cases hall : ∀ T : ℝ, 0 ≤ T → C.DefinedUpTo T
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨T, hT, hTbad⟩ := hall
    set B : Set ℝ := {t : ℝ | 0 ≤ t ∧ ¬ C.DefinedUpTo t} with hBdef
    have hne : B.Nonempty := ⟨T, hT, hTbad⟩
    have hbdd : BddBelow B := ⟨0, fun x hx => hx.1⟩
    have hs0 : 0 ≤ sInf B := le_csInf hne (fun x hx => hx.1)
    have hgood : ∀ S : ℝ, 0 ≤ S → S < sInf B → C.DefinedUpTo S := by
      intro S hS hSs
      by_contra h
      exact absurd (csInf_le hbdd (show S ∈ B from ⟨hS, h⟩)) (not_le.mpr hSs)
    -- the infimum is not itself reached
    have hbad : ¬ C.DefinedUpTo (sInf B) := by
      intro hdef
      obtain ⟨T', hlt, hT'⟩ := C.extend_forward (sInf B) hs0 hdef
      obtain ⟨c, hcB, hcT'⟩ := exists_lt_of_csInf_lt hne hlt
      exact hcB.2 (C.definedUpTo_mono hcB.1 hcT'.le hT')
    -- hence it is positive, since the initial time is reached
    have hpos : 0 < sInf B := by
      rcases eq_or_lt_of_le hs0 with h | h
      · exact absurd (h ▸ C.definedUpTo_zero) hbad
      · exact h
    -- and infinitely many surgeries occur up to it
    have hinf : ¬ (C.surgeryTimes ∩ Iic (sInf B)).Finite := by
      intro hfin
      exact hbad (C.extend_limit (sInf B) hpos hgood hfin)
    exact ⟨sInf B, hpos, hgood, hbad, hinf⟩
