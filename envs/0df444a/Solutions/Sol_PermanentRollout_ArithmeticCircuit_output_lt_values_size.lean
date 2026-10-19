-- Prove2me | solution 1 for PermanentRollout.ArithmeticCircuit.output_lt_values_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/e6bdcc90-73f2-47e5-950e-3c074649d932

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_CircuitPrefix_values_size
import Theorems.Thm_PermanentRollout_ArithmeticCircuit_values_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.ArithmeticCircuit
namespace PermanentRollout.ArithmeticCircuit
theorem _root_.solution {ι : Type}
    (circuit : ArithmeticCircuit ι) :
    circuit.output < circuit.values.size := by
  simpa [values_size circuit] using circuit.output_lt
end PermanentRollout.ArithmeticCircuit
