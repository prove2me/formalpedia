-- Prove2me | solution 1 for PermanentRollout.permanent_superquadratic_of_logarithmic_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/011c7062-e625-46b7-8a62-e628eff29513

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_superquadratic_of_logarithmic_degree_bounds

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (hbound : ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuitComplexity (permanent n) : ℝ)) :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ (circuitComplexity (permanent n) : ℝ) := by
  exact superquadratic_of_logarithmic_degree_bounds
    (fun n => circuitComplexity (permanent n)) hbound
end PermanentRollout
