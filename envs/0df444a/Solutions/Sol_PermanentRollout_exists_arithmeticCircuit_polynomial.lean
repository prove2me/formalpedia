-- Prove2me | solution 1 for PermanentRollout.exists_arithmeticCircuit_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/736a7ce8-bc26-49a3-b15b-c13c1305b83e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_CircuitPrefix_exists_extension_computing

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {ι : Type}
    (polynomial : MvPolynomial ι ℂ) :
    ∃ circuit : ArithmeticCircuit ι,
      circuit.polynomial = polynomial := by
  obtain ⟨state, output, _, houtput, hpolynomial, _⟩ :=
    CircuitPrefix.exists_extension_computing polynomial
      (CircuitPrefix.empty ι)
  let circuit : ArithmeticCircuit ι :=
    ⟨state.program, output, houtput, state.valid⟩
  refine ⟨circuit, ?_⟩
  exact hpolynomial
end PermanentRollout
