-- Prove2me | solution 1 for PermanentRollout.permanent_circuit_loglog_bigOmega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/5ed099f6-642d-4ac7-90c3-f88cbaf92d47

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_circuit_loglog_lower_bound_288

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
        (circuitComplexity (permanent n) : ℝ) := by
  exact ⟨1 / 288, by norm_num, 2 ^ 64,
    fun n hn => permanent_circuit_loglog_lower_bound_288 hn⟩
end PermanentRollout
