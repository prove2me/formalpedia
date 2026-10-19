-- Prove2me | solution 1 for PermanentRollout.permanent_logarithmic_bounds_of_circuit_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/7731f857-2b6f-41b6-8e0f-5d7a56ac3ad8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_real_le_circuitComplexity_iff
import Theorems.Thm_PermanentRollout_permanent_circuit_logarithmic_bound_of_gradient

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
    ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuitComplexity (permanent n) : ℝ) := by
  intro d hd
  obtain ⟨N, hN⟩ := hgradient d hd
  refine ⟨max N (6 * blockWidth d), fun n hn => ?_⟩
  have hn_gradient : N ≤ n := le_trans (le_max_left _ _) hn
  have hn_source : 6 * blockWidth d ≤ n :=
    le_trans (le_max_right _ _) hn
  apply (real_le_circuitComplexity_iff (permanent n) _).2
  intro circuit hcircuit
  exact permanent_circuit_logarithmic_bound_of_gradient hd hn_source
    circuit hcircuit (hN n hn_gradient circuit hcircuit)
end PermanentRollout
