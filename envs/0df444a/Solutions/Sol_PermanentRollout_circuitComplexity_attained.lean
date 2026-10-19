-- Prove2me | solution 1 for PermanentRollout.circuitComplexity_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/83da011e-3384-4f6a-872a-662da6d72a24

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_arithmeticCircuit_polynomial
import Theorems.Thm_PermanentRollout_circuitComplexity_attained_of_exists

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
      circuit.polynomial = polynomial ∧
        circuit.size = circuitComplexity polynomial := by
  exact circuitComplexity_attained_of_exists polynomial
    (exists_arithmeticCircuit_polynomial polynomial)
end PermanentRollout
