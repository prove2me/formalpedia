-- Prove2me | solution 1 for PermanentRollout.ArithmeticCircuit.polynomial_eq_getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/8b2fa429-412a-44b9-a41e-d3b9e4684edc

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.ArithmeticCircuit
namespace PermanentRollout.ArithmeticCircuit
theorem _root_.solution {ι : Type}
    (circuit : ArithmeticCircuit ι)
    (houtput : circuit.output < circuit.values.size) :
    circuit.polynomial =
      circuit.values[circuit.output]'houtput := by
  simp [ArithmeticCircuit.polynomial, Array.getD_eq_getD_getElem?,
    houtput]
end PermanentRollout.ArithmeticCircuit
