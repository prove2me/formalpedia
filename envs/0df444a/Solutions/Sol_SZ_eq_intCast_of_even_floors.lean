-- Prove2me | solution 1 for SZ.eq_intCast_of_even_floors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:20.95245+00:00
-- url     : https://prove2.me/submissions/92207888-5ad4-4967-93e4-4cfb62023134

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
import Theorems.Thm_SZ_fract_eq_zero_of_even_floors

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {t : ℝ} (h : ∀ k : ℕ, Even ⌊t * 2 ^ k⌋) :
    ∃ z : ℤ, Even z ∧ t = (z : ℝ) := by
  refine ⟨⌊t⌋, by simpa using h 0, ?_⟩
  have hf := fract_eq_zero_of_even_floors h
  rw [Int.fract] at hf
  linarith
end SZ
