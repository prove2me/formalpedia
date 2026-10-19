-- Prove2me | solution 1 for PermanentRollout.source_fixedDegree_permanent_circuit_logarithmic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/155fb8a8-e364-4965-9c3d-d38629edf79d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_circuit_logarithmic_bound_of_gradient
import Theorems.Thm_PermanentRollout_permanent_circuit_gradient_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n)) :
    3 ≤ d →
    6 * blockWidth d ≤ n →
    4 * powerSumParameter d ≤ blockWidth d * blockColumns n d →
    circuit.polynomial = permanent n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
        (circuit.size : ℝ) := by
  intro hd hn hscale hpermanent
  exact permanent_circuit_logarithmic_bound_of_gradient
    hd hn circuit hpermanent
    (permanent_circuit_gradient_bound hd hn hscale circuit hpermanent)
end PermanentRollout
