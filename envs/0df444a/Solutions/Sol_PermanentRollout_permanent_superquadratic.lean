-- Prove2me | solution 1 for PermanentRollout.permanent_superquadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/0d21ea7d-4253-4826-ba86-3894b5ce41a8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_eventual_source_parameter_bounds
import Theorems.Thm_PermanentRollout_permanent_superquadratic_of_circuit_gradient
import Theorems.Thm_PermanentRollout_permanent_circuit_gradient_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ (circuitComplexity (permanent n) : ℝ) := by
  apply permanent_superquadratic_of_circuit_gradient
  intro d hd
  obtain ⟨N, hN⟩ := exists_eventual_source_parameter_bounds hd
  refine ⟨N, ?_⟩
  intro n hn circuit hpermanent
  obtain ⟨hlarge, _, hscale, _⟩ := hN n hn
  exact permanent_circuit_gradient_bound
    hd hlarge hscale circuit hpermanent
end PermanentRollout
