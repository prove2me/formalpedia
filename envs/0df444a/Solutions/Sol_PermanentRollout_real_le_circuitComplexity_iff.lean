-- Prove2me | solution 1 for PermanentRollout.real_le_circuitComplexity_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/26d99d94-906d-4ba1-8e8e-5810d8930f5a

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
    (bound : ℝ) :
    bound ≤ (circuitComplexity polynomial : ℝ) ↔
      ∀ circuit : ArithmeticCircuit ι,
        circuit.polynomial = polynomial → bound ≤ (circuit.size : ℝ) := by
  constructor
  · intro hbound circuit hcircuit
    exact hbound.trans (by
      exact_mod_cast circuitComplexity_le_of_circuit circuit hcircuit)
  · intro hbound
    obtain ⟨circuit, hpolynomial, hsize⟩ :=
      circuitComplexity_attained polynomial
    simpa [hsize] using hbound circuit hpolynomial
end PermanentRollout
