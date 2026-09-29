-- Prove2me | solution 1 for OpenGA.SurgeryContinuationData.definedUpTo_of_locallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T18:38:17.211852+00:00
-- url     : https://prove2.me/submissions/c472e7f8-549f-450b-b124-b4cee5bc40d6

import Definitions.Def_OpenGA_SurgeryContinuationData
import Mathlib.Tactic

set_option autoImplicit false

open Set

theorem solution (C : OpenGA.SurgeryContinuationData)
    (hfin : ∀ T : ℝ, (C.surgeryTimes ∩ Iic T).Finite) (T : ℝ) (hT : 0 ≤ T) :
    C.DefinedUpTo T := by
  by_contra hbad
  set B : Set ℝ := {t : ℝ | 0 ≤ t ∧ ¬ C.DefinedUpTo t} with hBdef
  have hne : B.Nonempty := ⟨T, hT, hbad⟩
  have hbdd : BddBelow B := ⟨0, fun x hx => hx.1⟩
  have hs0 : 0 ≤ sInf B := le_csInf hne (fun x hx => hx.1)
  have hgood : ∀ S : ℝ, 0 ≤ S → S < sInf B → C.DefinedUpTo S := by
    intro S hS hSs
    by_contra h
    exact absurd (csInf_le hbdd (show S ∈ B from ⟨hS, h⟩)) (not_le.mpr hSs)
  have hdef : C.DefinedUpTo (sInf B) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; exact C.definedUpTo_zero
    · exact C.extend_limit (sInf B) h hgood (hfin _)
  obtain ⟨T', hlt, hT'⟩ := C.extend_forward (sInf B) hs0 hdef
  obtain ⟨c, hcB, hcT'⟩ := exists_lt_of_csInf_lt hne hlt
  exact hcB.2 (C.definedUpTo_mono hcB.1 hcT'.le hT')
