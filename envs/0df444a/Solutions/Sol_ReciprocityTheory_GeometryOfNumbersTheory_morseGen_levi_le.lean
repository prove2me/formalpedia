-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morseGen_levi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:00.530714+00:00
-- url     : https://prove2.me/submissions/2b486bb4-a7cb-4d80-bbe6-6900efe816df

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
theorem _root_.solution {D : ℕ} (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (B z z + B (I • z) (I • z)) / 4 ≤ ‖B‖ / 2 * ‖z‖ ^ 2 := by
  have h1 : B z z ≤ ‖B‖ * ‖z‖ * ‖z‖ := (le_abs_self _).trans (B.le_opNorm₂ z z)
  have h2 : B (I • z) (I • z) ≤ ‖B‖ * ‖I • z‖ * ‖I • z‖ :=
    (le_abs_self _).trans (B.le_opNorm₂ _ _)
  have hI : ‖I • z‖ = ‖z‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hI] at h2
  nlinarith
end ReciprocityTheory.GeometryOfNumbersTheory
