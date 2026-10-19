-- Prove2me | solution 1 for PermanentRollout.ArithmeticCircuit.values_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/69881f36-26ca-4970-b339-b561ff7a9aeb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_size
import Theorems.Thm_PermanentRollout_CircuitPrefix_forwardFold_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.ArithmeticCircuit
namespace PermanentRollout.ArithmeticCircuit
theorem _root_.solution {ι : Type} (circuit : ArithmeticCircuit ι) :
    circuit.values.size = circuit.program.length := by
  simpa [ArithmeticCircuit.values] using
    CircuitPrefix.forwardFold_size circuit.program
      (#[] : Array (MvPolynomial ι ℂ))
end PermanentRollout.ArithmeticCircuit
