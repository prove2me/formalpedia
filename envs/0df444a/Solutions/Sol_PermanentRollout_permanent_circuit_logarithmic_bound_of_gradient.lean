-- Prove2me | solution 1 for PermanentRollout.permanent_circuit_logarithmic_bound_of_gradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/2b0c50d3-d9fa-42fc-bb7c-b2fb362e54bf

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_logarithmic_lower_bound_of_gradient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d) (hn : 6 * blockWidth d ≤ n)
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (_hpermanent : circuit.polynomial = permanent n)
    (hgradient :
      (sliceRank n d : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤
        3 * (circuit.size : ℝ)) :
    (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤
      (circuit.size : ℝ) := by
  exact logarithmic_lower_bound_of_gradient hd hn hgradient
end PermanentRollout
