-- Prove2me | solution 1 for add_one_inv_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:49.397997+00:00
-- url     : https://prove2.me/submissions/35175b36-b4a3-4a22-8a1e-aca2ab277629

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_add_one_div_pow_le_exp

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution {n : ℕ} : (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 := by
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  simpa using add_one_div_pow_le_exp (t := 1) hn₀ (by positivity)
