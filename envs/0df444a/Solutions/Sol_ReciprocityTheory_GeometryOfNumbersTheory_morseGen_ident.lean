-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morseGen_ident
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:56.128856+00:00
-- url     : https://prove2.me/submissions/cc214504-3322-4df2-84bc-dd3b85f8bfb3

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory Complex
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (fz qz : ℂ) (φz φ0 νz ν0 : ℝ) (n : ℕ) :
    ‖fz * cexp (-(n : ℂ) * qz / 2)‖ ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) * (νz / ν0) =
      ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * φz)) * νz * (Real.exp ((n : ℝ) * φ0) / ν0) := by
  have hre : (-(n : ℂ) * qz / 2).re = -((n : ℝ) * qz.re) / 2 := by simp
  have e1 : Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) =
      Real.exp (-((n : ℝ) * φz)) * Real.exp ((n : ℝ) * φ0) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, Complex.norm_exp, hre, mul_pow]
  calc ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))
        * (νz / ν0)
      = ‖fz‖ ^ 2 * (Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 *
          Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))) * (νz / ν0) := by ring
    _ = _ := by rw [e1]; ring
end ReciprocityTheory.GeometryOfNumbersTheory
