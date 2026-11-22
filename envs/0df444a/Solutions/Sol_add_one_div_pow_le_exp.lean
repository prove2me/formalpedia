-- Prove2me | solution 1 for add_one_div_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:02.551096+00:00
-- url     : https://prove2.me/submissions/ca82641e-4be5-4bf8-b7ee-28aa2dc657b0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution {t : ℝ} {n : ℕ} (hn : n ≠ 0) (ht : 0 ≤ 1 + t / n) :
    (1 + t / n) ^ n ≤ Real.exp t := by
  grw [add_comm, Real.add_one_le_exp, ← Real.exp_nat_mul, mul_div_cancel₀ _ (by simpa)]
  rwa [add_comm]
