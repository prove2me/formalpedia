-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.circuit_values_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/104df10d-e660-46cb-b221-df7ecd374cb2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι) :
    circuit.values.size = circuit.program.length := by
  change
    (circuit.program.foldl forwardStep
      (#[] : Array (MvPolynomial ι ℂ))).size = circuit.program.length
  simpa using
    forwardFold_size circuit.program (#[] : Array (MvPolynomial ι ℂ))
end PermanentRollout.ReverseAdjoint
