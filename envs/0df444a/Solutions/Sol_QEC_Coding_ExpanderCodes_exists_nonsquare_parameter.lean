-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_nonsquare_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:46.727984+00:00
-- url     : https://prove2.me/submissions/8665a1bc-1cc7-49ce-a4d7-0285bcd939dd

import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (F : Type*) [Field F] [Finite F]
    (hTwo : ringChar F ≠ 2) :
    ∃ epsilon : F, epsilon ≠ 0 ∧ ∀ r : F, r ^ 2 ≠ epsilon := by
  obtain ⟨epsilon, hNonSquare⟩ := FiniteField.exists_nonsquare hTwo
  refine ⟨epsilon, ?_, ?_⟩
  · rintro rfl
    exact hNonSquare ⟨0, by simp⟩
  · intro r hSquare
    exact hNonSquare ⟨r, by simpa only [pow_two] using hSquare.symm⟩
end QEC.Coding.ExpanderCodes
