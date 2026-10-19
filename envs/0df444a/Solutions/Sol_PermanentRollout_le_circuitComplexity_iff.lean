-- Prove2me | solution 1 for PermanentRollout.le_circuitComplexity_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/571e402a-58fc-40f9-ab65-62bfad8dcdc3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_circuitComplexity_le_of_circuit
import Theorems.Thm_PermanentRollout_circuitComplexity_attained

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {ι : Type}
    (polynomial : MvPolynomial ι ℂ)
    (bound : ℕ) :
    bound ≤ circuitComplexity polynomial ↔
      ∀ circuit : ArithmeticCircuit ι,
        circuit.polynomial = polynomial → bound ≤ circuit.size := by
  constructor
  · intro hbound circuit hcircuit
    exact hbound.trans (circuitComplexity_le_of_circuit circuit hcircuit)
  · intro hbound
    obtain ⟨circuit, hpolynomial, hsize⟩ :=
      circuitComplexity_attained polynomial
    simpa [hsize] using hbound circuit hpolynomial
end PermanentRollout
