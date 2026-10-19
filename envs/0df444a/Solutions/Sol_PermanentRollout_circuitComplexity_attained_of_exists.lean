-- Prove2me | solution 1 for PermanentRollout.circuitComplexity_attained_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/48fb8215-742c-4403-8fb3-6868008eeb80

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {ι : Type}
    (polynomial : MvPolynomial ι ℂ)
    (hrepresentable : ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial) :
    ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial ∧
        circuit.size = circuitComplexity polynomial := by
  have hnonempty :
      {size : ℕ | ∃ circuit : ArithmeticCircuit ι,
        circuit.polynomial = polynomial ∧ circuit.size = size}.Nonempty := by
    obtain ⟨circuit, hcircuit⟩ := hrepresentable
    exact ⟨circuit.size, circuit, hcircuit, rfl⟩
  exact Nat.sInf_mem hnonempty
end PermanentRollout
