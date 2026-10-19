-- Prove2me | solution 1 for PermanentRollout.permanent_superquadratic_of_circuit_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/c4677982-33d4-4a82-95c1-90b6f6df0fd2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_logarithmic_bounds_of_circuit_gradient
import Theorems.Thm_PermanentRollout_permanent_superquadratic_of_logarithmic_bounds

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (hgradient : ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ circuit : ArithmeticCircuit (Fin n × Fin n),
        circuit.polynomial = permanent n →
          (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
            3 * (circuit.size : ℝ)) :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ (circuitComplexity (permanent n) : ℝ) := by
  exact permanent_superquadratic_of_logarithmic_bounds
    (permanent_logarithmic_bounds_of_circuit_gradient hgradient)
end PermanentRollout
