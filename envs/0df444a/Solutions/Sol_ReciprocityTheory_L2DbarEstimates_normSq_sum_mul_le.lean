-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.normSq_sum_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:35.907859+00:00
-- url     : https://prove2.me/submissions/8033ce68-aeb7-4d88-b144-1c6f15576f50

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    Complex.normSq (∑ q ∈ s, a q * b q) ≤
      (∑ q ∈ s, Complex.normSq (a q)) * ∑ q ∈ s, Complex.normSq (b q) := by
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ * ‖b q‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _
end ReciprocityTheory.L2DbarEstimates
