-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_inputAdjoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/74dcb081-4237-4da4-aeb4-da61a2766874

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_run_inputAdjoints
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_run_realizes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
open PermanentRollout.ReverseAdjoint.CircuitAdjoint
namespace PermanentRollout.ReverseAdjoint.CircuitAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) (houtput : output ∈ circuit.outputs)
    (input : ι) :
    ((run circuit output).inputAdjoints input).eval
      (run circuit output).circuit.values =
        MvPolynomial.pderiv input (output.eval circuit.values) := by
  calc
    ((run circuit output).inputAdjoints input).eval
        (run circuit output).circuit.values =
      (ReverseAdjoint.run circuit output).inputAdjoints input :=
        (run_realizes circuit output).2.1 input
    _ = MvPolynomial.pderiv input (output.eval circuit.values) :=
      ReverseAdjoint.run_inputAdjoints circuit output houtput input
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
